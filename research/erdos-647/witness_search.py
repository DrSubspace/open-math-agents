"""GPU witness search for Erdős 647. Python 3, NumPy, PyOpenCL and python-flint.

All indices are relative to the first tested n. The GPU only applies small-prime
divisibility exclusions. The CPU checks the original divisor inequalities.
"""
import argparse
import hashlib
import json
from math import isqrt, prod
from pathlib import Path
from time import monotonic

import numpy as np
import pyopencl as cl
from flint import fmpz

SHIFTS = (1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 20, 24)
DENSE_STEP = 360360
START = 10**22 + 1


def primes_to(limit):
    a = bytearray([1]) * (limit+1)
    a[:2] = bytes(2)
    for p in range(2, isqrt(limit)+1):
        if a[p]:
            a[p*p::p] = bytes((limit-p*p)//p+1)
    return [p for p in range(2, limit+1) if a[p]]


def max_smooth(k, budget):
    primes = [p for p in primes_to(k) if k % p == 0]
    def visit(i, v, count):
        if i == len(primes):
            return v if v % k == 0 else 0
        p = primes[i]
        return max(visit(i+1, v*p**e, count*(e+1))
                   for e in range(budget//count))
    return visit(0, 1, 1)


def check_exclusion_rule(bound):
    sizes = []
    for k in SHIFTS:
        tau = sum(k % i == 0 for i in range(1, k+1))
        assert 2520 % k == 0 and 4*tau > k+2
        for e in range(1, (k+2)//tau):
            sizes.append(k + bound**e * max_smooth(k, (k+2)//(e+1)))
    assert max(sizes) < START
    for p in (11, 13):
        assert {k % p for k in SHIFTS} == set(range(1,p))
    return max(sizes)


def first_multiple(lo, step):
    return lo + (-lo) % step


def largest_tau(n):
    # Compress a factorization onto successive primes in descending exponent order.
    ps = []
    primorial = 1
    for p in primes_to(max(100, n.bit_length()*2)):
        primorial *= p
        if primorial > n:
            break
        ps.append(p)
    def best(i, room, emax, divisors):
        ans = divisors
        if i == len(ps):
            return ans
        p = ps[i]
        for e in range(1, emax+1):
            room //= p
            if not room:
                break
            ans = max(ans, best(i+1, room, e, divisors*(e+1)))
        return ans
    return best(0, n, n.bit_length(), 1)


def evaluate(n):
    # Given n divisible by 2520, n-1 is 3 mod 4. A composite n-1 has >=4 divisors.
    if not fmpz(n-1).is_prime():
        return 1
    k, stop = 2, n-1
    while k <= stop:
        m = n-k
        if k in SHIFTS:
            c = m
            multiplier = 1
            for p in (2,3,5):
                e = 0
                while c % p == 0:
                    c //= p
                    e += 1
                multiplier *= e+1
            allowed = (k+2)//multiplier
            assert allowed <= 3
            passes = c == 1 and allowed >= 1
            if not passes and allowed >= 2:
                passes = bool(fmpz(c).is_prime())
            if not passes and allowed == 3:
                root = isqrt(c)
                passes = root*root == c and bool(fmpz(root).is_prime())
            if not passes:
                return k
        elif prod(int(e)+1 for _,e in fmpz(m).factor()) > k+2:
            return k
        if k == 128:
            stop = min(stop, largest_tau(n)-3)
        k += 1
    return 0


def wheel(base, step, primes):
    residues = np.array([0],dtype=np.uint64)
    period = 1
    for p in primes:
        offsets = (residues[:,None] + period*np.arange(p,dtype=np.uint64)).ravel()
        forbidden = {(k-base)*pow(step,-1,p) % p for k in SHIFTS}
        allowed = np.ones(p,dtype=bool)
        allowed[list(forbidden)] = False
        residues = offsets[allowed[offsets % p]]
        period *= p
    return period, np.sort(residues)


class Sieve:
    def __init__(self, base, step, bound, wheel_count):
        self.base, self.step = base, step
        ps = primes_to(bound)
        # A prime dividing the step must never divide one of these shifted values,
        # except for primes <= 7, which play a different role in the proof.
        assert all(all((base-k) % p for k in SHIFTS) for p in ps if p>7 and step%p==0)
        active = [p for p in ps if p > 7 and step%p]
        self.active = active
        period, residues = wheel(base, step, active[:wheel_count])
        self.period, self.width = period, len(residues)
        tables, checks, pos = [], [], 0
        for p in active[wheel_count:]:
            if p > 509:
                break
            arr = np.arange(p,dtype=np.int64)
            bad = [(k-base)*pow(step,-1,p) % p for k in SHIFTS]
            good = np.ones(p,dtype=np.uint32)
            good[bad] = 0
            mask = np.zeros(p,dtype=np.uint32)
            for bit in range(32):
                mask |= good[(arr + period*bit) % p] << np.uint32(bit)
            tables.append(mask)
            checks.append(f"bits &= masks[{pos} + (t % {p}UL)];")
            if len(checks) in (4, 10, 20, 36, 60):
                checks.append("if (!bits) return;")
            pos += p

        tails, divisors, starts, reciprocals, pos = [], [], [], [], 0
        for p in active:
            if p <= 509:
                continue
            bitmap = np.zeros((p+31)//32,dtype=np.uint32)
            for k in SHIFTS:
                r = (k-base)*pow(step,-1,p)%p
                bitmap[r//32] |= np.uint32(1 << (r%32))
            tails.append(bitmap)
            divisors.append(p)
            starts.append(pos)
            reciprocals.append(2**64//p)
            pos += len(bitmap)
        platforms = cl.get_platforms()
        devices = [d for plat in platforms for d in plat.get_devices(device_type=cl.device_type.GPU)]
        dev = max(devices, key=lambda d:d.max_compute_units)
        self.ctx = cl.Context([dev])
        self.queue = cl.CommandQueue(self.ctx)
        self.device = dev.name
        self.group_threads = 1 << 20
        self.capacity = 1 << 20
        flags = cl.mem_flags
        def read_buffer(data):
            return cl.Buffer(self.ctx,flags.READ_ONLY | flags.COPY_HOST_PTR,hostbuf=data)
        self.residues = read_buffer(residues)
        self.masks = read_buffer(np.concatenate(tables))
        self.bitmap = read_buffer(np.concatenate(tails))
        self.p = read_buffer(np.array(divisors,dtype=np.uint32))
        self.offsets = read_buffer(np.array(starts,dtype=np.uint32))
        self.recip = read_buffer(np.array(reciprocals,dtype=np.uint64))
        self.first = cl.Buffer(self.ctx,flags.READ_WRITE,self.capacity*8)
        self.final = cl.Buffer(self.ctx,flags.READ_WRITE,self.capacity*8)
        self.hits = cl.Buffer(self.ctx,flags.READ_WRITE,4)
        self.kept = cl.Buffer(self.ctx,flags.READ_WRITE,4)
        source = """
        __kernel void presieve(ulong offset, ulong limit, __global const ulong *residues,
                __global const uint *masks, __global ulong *out, __global uint *hits) {
            ulong thread = offset + get_global_id(0);
            ulong t = residues[thread % WIDTH] + (thread / WIDTH) * (32UL*PERIOD);
            if(t>=limit) return;
            uint bits = 0xffffffff;
            CHECKS
            while(bits) {
                uint pos = 31-clz(bits & (0u-bits));
                bits &= bits-1;
                ulong v = t + pos*PERIOD;
                if(v<limit) {
                    uint index = atomic_inc(hits);
                    if(index<CAPACITY) out[index] = v;
                }
            }
        }
        __kernel void finish(uint count,__global const ulong *a,__global const uint *ps,
                __global const uint *offsets,__global const ulong *recip,
                __global const uint *bitmap,__global ulong *out,__global uint *kept) {
            uint i = get_global_id(0);
            if(i>=count) return;
            ulong v=a[i];
            for(uint j=0;j<TAIL;j++) {
                uint p=ps[j];
                ulong q=mul_hi(v,recip[j]);
                uint r=(uint)(v-q*p);
                if(r>=p) r-=p;
                if(bitmap[offsets[j]+(r>>5)] & (1u<<(r & 31))) return;
            }
            out[atomic_inc(kept)]=v;
        }
        """
        for key,val in {"WIDTH":f"{self.width}UL","PERIOD":f"{period}UL","CHECKS":"\n".join(checks),
                        "TAIL":str(len(divisors)),"CAPACITY":str(self.capacity)}.items():
            source=source.replace(key,val)
        program = cl.Program(self.ctx,source).build()
        self.pre, self.finish = program.presieve, program.finish

    def batches(self, count):
        groups = (count+32*self.period-1)//(32*self.period)
        threads = groups*self.width
        assert count+32*self.period < 2**64 and self.capacity >= self.group_threads
        counter = np.zeros(1,dtype=np.uint32)
        for start in range(0,threads,self.group_threads):
            size = min(threads-start,self.group_threads)
            cl.enqueue_fill_buffer(self.queue,self.hits,np.uint32(0),0,4)
            self.pre(self.queue,(size,),None,np.uint64(start),np.uint64(count),
                     self.residues,self.masks,self.first,self.hits)
            cl.enqueue_copy(self.queue,counter,self.hits)
            nfirst = int(counter[0])
            if nfirst > self.capacity:
                raise RuntimeError(f"Increase output capacity for {nfirst} presieve hits")
            if not nfirst:
                yield np.array([],dtype=np.uint64)
                continue
            cl.enqueue_fill_buffer(self.queue,self.kept,np.uint32(0),0,4)
            self.finish(self.queue,(nfirst,),None,np.uint32(nfirst),self.first,self.p,
                        self.offsets,self.recip,self.bitmap,self.final,self.kept)
            cl.enqueue_copy(self.queue,counter,self.kept)
            tail = np.empty(int(counter[0]),dtype=np.uint64)
            if len(tail):
                cl.enqueue_copy(self.queue,tail,self.final)
            yield np.sort(tail)


def reference(sieve, count):
    keep = np.ones(count,dtype=bool)
    for p in sieve.active:
        inverse = pow(sieve.step,-1,p)
        for k in SHIFTS:
            keep[((k-sieve.base)*inverse % p)::p] = False
    return np.flatnonzero(keep).astype(np.uint64)


def run(lane, amount, bound, start):
    if bound < 521 or amount < 1:
        raise ValueError("Use a prime cutoff of at least 521 and a positive search size")
    limit = check_exclusion_rule(bound)
    if lane == "interval":
        step = DENSE_STEP
        count = (start+amount-1-first_multiple(start,step))//step+1
        w = 5
    else:
        step = 2**3*3*prod(primes_to(43))
        count = amount
        w = 3
    base = first_multiple(start,step)
    assert start >= START and step % 2520 == 0
    sieve = Sieve(base, step, bound, w)
    check = min(count,10_000_003)
    actual = np.sort(np.concatenate(list(sieve.batches(check)))) if check else np.array([], dtype=np.uint64)
    expected = reference(sieve,check)
    assert np.array_equal(actual,expected)
    print("reference",check,len(actual),"device",sieve.device,flush=True)
    hist = {}; best_k = 0; best = None; total = 0; witnesses = []
    fingerprint = 0
    then = monotonic()
    for values in sieve.batches(count):
        total += len(values)
        for u in values:
            idx = int(u)
            fingerprint ^= int.from_bytes(hashlib.sha256(str(idx).encode()).digest(),"big")
            n = base + step*idx
            k = evaluate(n)
            hist[k] = hist.get(k,0)+1
            if k == 0:
                witnesses.append(n)
            elif k > best_k or (k == best_k and n < best):
                best_k,best = k,n
    record = dict(lane=lane, start=start, amount=amount, first=base, step=step, count=count,
                  last=base+step*(count-1) if count else None, small_prime_limit=bound, exception_bound=limit,
                  survivors=total, histogram=hist, first_failure_of_best=best_k,best=best,
                  xor_sha256=f"{fingerprint:064x}",witnesses=witnesses,
                  cpu_reference=[check,len(actual)],seconds=round(monotonic()-then,2))
    if best:
        record["best_factorizations"] = [
            [k,[[int(p),int(e)] for p,e in fmpz(best-k).factor()]]
            for k in range(1,best_k+1)]
        for k, factors in record["best_factorizations"]:
            assert all(fmpz(p).is_prime() for p,_ in factors)
            assert prod(p**e for p,e in factors)==best-k
            assert (prod(e+1 for _,e in factors) <= k+2) == (k < best_k)
    return record


if __name__ == "__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("lane",choices=["interval","targeted"])
    ap.add_argument("amount",type=int,help="integer interval width, or number of targeted multipliers")
    ap.add_argument("--bound",type=int,default=65521)
    ap.add_argument("--start",type=int,default=START)
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    record=run(args.lane,args.amount,args.bound,args.start)
    data=json.dumps(record,indent=2)
    if args.output: args.output.write_text(data+"\n",encoding="utf8")
    print(json.dumps({k:v for k,v in record.items() if k != "best_factorizations"}))
