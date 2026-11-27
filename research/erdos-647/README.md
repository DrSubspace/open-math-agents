# Searching for a witness to Erdős problem 647

For a witness, every integer shift `1 ≤ k < n` must satisfy `τ(n−k) ≤ k+2`, where τ counts positive divisors. This search found no witness in the complete interval **10²² < n ≤ 10²² + 10¹⁹**. A second search tested a sparse progression at larger values. The existence of a witness greater than 24 remains open. A previous project reports covering all values through 10²². [Problem statement](https://www.erdosproblems.com/647) · [Previous computation](https://github.com/veljjanoski/erdos647)

## Complete interval

The interval contains 27,750,027,750,027 multiples of 360,360. All other integers in it are excluded by the necessary divisibility conditions below. The OpenCL sieve on an RTX 5090 retained 205,752 multiples. Exact arithmetic on the CPU gave a violating shift for every one. Among these survivors, the longest passing prefix was 11 shifts. One integer attaining it was 10,001,733,060,305,656,870,200. At shift 12 its predecessor has 48 divisors and the limit is 14. Factorizations for shifts 1 through 12 appear in the result file. [Interval results](interval.json)

A full replay changed the number of wheel primes from five to four and reproduced the survivor count and fingerprint. An alternative CPU check eliminated 205,751 survivors by a forbidden multiplier, a common small factor, or a failed Fermat congruence for a required prime. The last survivor was eliminated by counting distinct verified divisors. Separate array-based CPU sieves agreed with the GPU at the beginning, middle, and end of the interval. These three comparisons used a shallower cutoff of 521 to produce positive controls and recovered 24, 16, and 21 survivors respectively. Both full runs share OpenCL kernel source. The replay and the smaller CPU checks are computational evidence. [Replay results](audit.json)

The exceptional survivor, 10,005,973,510,515,888,185,280, really passes all thirteen fixed prime-cofactor requirements. Its first failure is at shift 7, where n−7 = 7² · 105,499,529 · 1,935,587,229,313 has 12 divisors against a limit of 9. It also illustrates the extra test derived below. Here 16 divides n and n−16 has 40 divisors against a limit of 18.

## Targeted progression

We tested 549,755,813,888 consecutive multiples of 313,986,271,960,080,720, starting just above 10²² and ending at 172,615,788,490,907,878,654,427,809,920. The step is 24 times the product of the primes through 43. It makes many nearby shifted integers avoid small prime factors automatically. The sieve retained 577,083 candidates, and every one failed an original inequality by shift 12. The least sieve survivor attaining the longest passing prefix was 32,050,800,247,224,883,987,537,955,280. At shift 12 it has 24 divisors against a limit of 14. A separate CPU sieve agreed with the GPU on the first 10,000,003 progression indices, including all ten survivors. Coverage beyond the complete interval is limited to this progression. [Targeted results](targeted.json)

## Why the sieve may discard an integer

Earlier work established the divisibility restrictions used here. The following elementary calculation independently recovers the entire 360,360 restriction. [Hughes reduction](https://github.com/scottdhughes/erdos647-proof-chain) · [Previous work on the thirteen shifts](https://lefttosolve.com/p/Erdos647.erdos_647/agent.txt)

Start with M = 1 and assume M divides n. Take P successively from 2, 4, 8, 3, 9, 5, 7, 11, 13. For each possible nonzero residue r of n modulo P, choose a shift k from the set K below with k dividing M and k ≡ r modulo P. Then a = lcm(k,P) divides n−k. Whenever 2τ(a) > k+2, any prime factor of n−k outside the prime factors of a forces failure at k. The remaining possible values of n−k are multiples of a supported on its primes with divisor count at most k+2. Enumerating these finite lists gives respective upper bounds on n of 5, 10, 36, 10, 84, 26, 96, 2,196, and 4,080 for the nonzero residues at each step. For example, at P = 8 the only nonzero residue after 4 divides n is 4. Then 8 divides n−4, and τ(n−4) ≤ 6 forces n−4 to be a power of 2 at most 32.

For n > 4,080, every step therefore gives P dividing n, and we replace M with lcm(M,P). The final M is 360,360. Direct divisor counts rule out every n from 25 through 4,080. The enumeration and the small cases take a fraction of a second in ordinary Python. [Divisibility check](cofactor_check.py)

Let `K = {1,2,3,4,5,6,8,9,10,12,18,20,24}`. Each k in K divides 2,520 and satisfies `4τ(k) > k+2`. Thus k divides m = n−k. If a prime p > 7 divides m and there is any other prime outside the primes of k and p, then τ(m) ≥ 4τ(k), which disqualifies n. Consequently, for a possible witness with p dividing m, we may write m = d pᵉ, where k divides d, every prime of d divides k, and `(e+1)τ(d) ≤ k+2`. Enumerating the possible exponents of d and e gives `k + d pᵉ ≤ 103,032,034,608` for p ≤ 65,521. The search starts above 10²². Any hit by a prime between 11 and 65,521 is therefore an exact exclusion.

Modulo each of 11 and 13, K covers every nonzero residue and omits zero. Avoiding all the hits forces both primes to divide n. Together with 2,520 this gives 360,360 dividing n. The GPU enumerates indices in the resulting arithmetic progression. It uses a wheel followed by bit masks for additional primes. On the CPU, proven primality and integer factorization test the original inequalities on each survivor. [Search implementation](witness_search.py)

## A fourteenth required prime cofactor

For n > 10²² satisfying the inequalities, all thirteen n−k with k in K have the form d⋅q with q a prime greater than 120 and d drawn from a finite shift-specific list. **One more shift necessarily has this same property.**

| Condition on n | Extra shift k | A divisor a of n−k | τ(a) | k+2 |
|---|---:|---:|---:|---:|
| 16 divides n | 16 | 16 | 5 | 18 |
| n ≡ 56 mod 128 | 56 | 896 | 16 | 58 |
| n ≡ 120 mod 128 | 120 | 1,920 | 32 | 122 |

To see that these cases cover all possibilities, suppose 8 divides n exactly. Then n−8 has at least four factors of 2 counted with multiplicity. A pure power of 2 with at most ten divisors is too small here. Writing b for the exponent of 2 in n−8, its odd part gives `2(b+1) ≤ 10`. Hence b = 4 and n ≡ 24 mod 32. Now n−24 has at least five factors of 2 and exactly one of 3, since 9 divides n. Its part coprime to 6 must exceed one, since `τ(3⋅2ᵇ) ≤ 26` would force b ≤ 12. Thus `4(b+1) ≤ 26` at this shift forces b = 5. It follows that n ≡ 56 mod 64, giving the two remaining rows. Divisibility by 2,520 supplies the odd factors of a in the table.

For each fixed or extra shift, `4τ(a) > k+2`, with a = k for the thirteen fixed shifts. The part d of n−k supported on primes of a is a multiple of a with τ(d) ≤ k+2. There are finitely many such d. At most one additional prime q can occur, to exponent at most two. The accompanying standard-library script checks that even the largest d times 120² is too small. Thus an additional prime q > 120 must occur. It enumerates every d with the appropriate divisor budget and tests the congruence `k + d qᵉ ≡ n (mod 40320)` on all applicable residues, since 40,320 is the least common multiple of 2,520 and 128. This eliminates all cases e = 2 and prints the available multipliers for e = 1. The fourteen primes must be distinct: a prime common to two shifted integers divides their positive difference, at most 119. [Finite arithmetic check](cofactor_check.py)

The extra-shift square exclusions can also be verified by hand.

- At k = 16 a square cofactor leaves d = 16 or 32. The first would give q² ≡ 2 mod 3, the second q² ≡ 2 mod 5.
- At k = 56 the only choices are d = 128⋅7 or 256⋅7. They give q² ≡ 2 mod 3 or q² ≡ 2 mod 5, respectively.
- At k = 120 the choices are d = 2ᵇ⋅15 with b = 7, 8, 9. Reducing (n−120)/3 modulo 3 forces b even. With b = 8, reducing n−120 modulo 7 gives q² ≡ 5 mod 7.

## Reproduce

The run used Python 3.12 with NumPy 2.3.5, PyOpenCL 2026.1.5, python-flint 0.9.0, and an NVIDIA OpenCL runtime. Run these commands in this directory. The cofactor enumeration requires only the Python standard library.

```sh
python cofactor_check.py
python witness_search.py interval 10000000000000000000 --output interval.json
python witness_search.py targeted 549755813888 --output targeted.json
python audit_interval.py
```

The JSON files include exact endpoints, counts, the fingerprint of survivor indices, and factorizations for a longest-prefix survivor in each search. Read the large integers with arbitrary precision.
