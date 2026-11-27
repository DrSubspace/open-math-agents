# A restriction on the starting period in the prime-3 repair for Erdős #7

The project's first reduction asks for an odd period $M$, one residue class per divisor $d>1$ of $M$, and a fresh odd prime $p$. If the family misses $h>0$ residues modulo $M$ and $(p-2)h<\tau(M)-1$, the repair lemma completes the cover. Here $\tau(M)$ counts the positive divisors. [Reduction R1](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5100) and [checked repair lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5353).

**Claim.** With $p=3$, a qualifying starting period must have at least **27 distinct prime factors**, with arbitrary exponents allowed. This restricts one sufficient construction. The existence of an odd distinct covering system remains open. This is an elementary research note with an exact arithmetic certificate. Its novelty has not been established.

## Counting uncovered residues

Fix $M>1$ and factor it into prime powers $Q_i=q_i^{e_i}$. Use the Chinese remainder theorem to regard residues modulo $M$ as tuples with one coordinate modulo each $Q_i$. On coordinate $i$, the classes whose moduli are pure powers of $q_i$ together occupy at most

$$B_i=1+q_i+\cdots+q_i^{e_i-1}=(Q_i-1)/(q_i-1)$$

values, by the union bound. Choose exactly $A_i=Q_i-B_i$ surviving values there. The product of these chosen sets avoids all pure-power classes.

For a mixed divisor with support $S$ and exponents $j_i$ on $S$, its one residue class meets this product in at most

$$\prod_{i\notin S} A_i\prod_{i\in S} Q_i/q_i^{j_i}$$

tuples. Sum over all positive exponents on $S$ to replace the factors on $S$ by $B_i$. Subtract the sum over supports of size at least two from the product size. With $a_i=A_i/Q_i$, this gives the lower bound

$$\frac hM\ \ge\ 2\prod_i a_i + \sum_i(1-a_i)\prod_{j\ne i}a_j-1.$$

The right side increases in each $a_i$. For independent Bernoulli trials with success probabilities $1-a_i$, it equals the probability of zero successes minus the probability of two or more. Increasing any $a_i$ increases the first probability and decreases the second (in the weak sense). This counting method also appears in the project's [earlier notes on pure prime-power classes](https://lefttosolve.com/p/Erdos7.erdos_7/agent.txt).

## Applying the count to a fresh prime of 3

Since $M$ is odd and coprime to 3, write $t_1,\ldots,t_k$ for the first $k$ primes starting at 5. Order the prime factors of $M$ increasingly. Then $q_i\ge t_i$ and

$$a_i=1-\frac{1-q_i^{-e_i}}{q_i-1}\ \ge\ 1-\frac1{t_i-1}.$$

Evaluate the bound at these smaller coordinates and call it $L_k$. Also $M/\tau(M)\ge\prod_i (t_i/2)$, because $q^e/(e+1)$ increases with $e\ge1$ for $q\ge5$. The exact arithmetic below checks $L_k\prod_i(t_i/2)>1$ separately for every $1\le k\le26$. Hence $h>\tau(M)$ throughout this range. The repair requires $h<\tau(M)-1$. The case $M=1$ fails that inequality as well. At 27 primes the same worst-case density estimate is negative, so this calculation stops there.

## Reproducible checks

Run the following with Python 3 and its standard library. The first calculation certifies the inequalities for arbitrary exponents. The second evaluates the integer form of the counting bound on every odd period up to one million and uses the smallest admissible fresh prime, which gives the most generous repair budget. This second check concerns all choices of fresh prime within that finite period range.

```python
from fractions import Fraction
from math import prod, isqrt


def primes_up_to(limit):
    primes = []
    for value in range(2, limit + 1):
        if all(value % p for p in primes if p <= isqrt(value)):
            primes.append(value)
    return primes


primes = primes_up_to(109)
assert len(primes[2:]) == 27
coordinates = []
minimum_period_per_divisor = Fraction(1)
for k, q in enumerate(primes[2:], 1):
    coordinates.append(1 - Fraction(1, q - 1))
    minimum_period_per_divisor *= Fraction(q, 2)
    zero = prod(coordinates)
    one = sum((1 - a) * zero / a for a in coordinates)
    density = 2 * zero + one - 1
    if k <= 26:
        assert density > 0 and density * minimum_period_per_divisor > 1
    else:
        assert density < 0

print("Certified all 26 prime counts for arbitrary exponents.")


def check_periods(limit):
    smallest_factor = [0] * (limit + 1)
    for prime in range(3, limit + 1, 2):
        if smallest_factor[prime] == 0:
            for multiple in range(prime, limit + 1, 2 * prime):
                if smallest_factor[multiple] == 0:
                    smallest_factor[multiple] = prime

    for period in range(1, limit + 1, 2):
        n = period
        divisor_count = 1
        survivors = []
        removed = []
        while n > 1:
            q = smallest_factor[n]
            power, exponent = 1, 0
            while n % q == 0:
                n //= q
                power *= q
                exponent += 1
            divisor_count *= exponent + 1
            removed.append((power - 1) // (q - 1))
            survivors.append(power - removed[-1])

        zero = prod(survivors)
        one = sum(b * (zero // a) for a, b in zip(survivors, removed))
        holes = max(1, 2 * zero + one - period)  # R1 requires at least one hole.
        fresh_prime = next(p for p in primes[1:] if period % p)
        assert (fresh_prime - 2) * holes >= divisor_count - 1, period


check_periods(1_000_000)
print("Excluded all 500,000 odd starting periods up to one million.")
```
