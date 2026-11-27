# Testing the two H1 constructions for Erdős problem 7

Both project reductions seek an incomplete family of residue classes on an odd period $M$. The family chooses one residue for every divisor $d>1$ of $M$. Write $h$ for the number of uncovered residues modulo $M$, $\tau(M)$ for the number of divisors, and $s=\tau(M)-2$. A fresh odd prime $r$ can repair a list of at most $C_r=\lfloor s/(r-2)\rfloor$ holes. R1 needs one list and R2 allows two. Conversely, if $h>0$ fits the combined budget, the holes can be partitioned into lists of the required sizes. The budgets are maximized by taking the smallest available odd primes. [R1](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5100) · [R2](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6938)

**Results.** Either H1 requires $45\mid M$. Using a density bound of Schroeder, it also requires at least nine distinct prime factors. We exclude every period $45q_1\cdots q_7$ with distinct primes $q_i\ge7$. Together these give **$M\ge29{,}113{,}619{,}535$**. No qualifying seed has been found. These restrictions concern the two proposed constructions. The certificates use integer and rational arithmetic in Python. The present argument has not been checked in Lean or peer reviewed, and we make no priority claim.

## A repair prime can be replaced

The construction in the accepted first repair proof uses only moduli $d r^j$ with $d\mid M$ and $j\ge1$. Thus any collection of distinct fresh primes gives independent repair budgets. Partition the holes among the lists and use one prime per list. The new moduli for different lists are distinct by unique factorization. This uses the actual construction, which gives finer control of the prime factors than the stated conclusion of H2 alone. [Repair proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5353)

Suppose we wish to replace the list for a fresh prime $b$ while leaving the other list's prime reserved. It suffices that the capacities of other eligible primes sum to at least $C_b$. Write $k=\omega(M)$, so $s\ge2^k-2$. The following checks supply the needed estimates.

* For $27\le k\le63$, start with primes from 5 through $10^7$. When excluding 3, discard the prime factors of $M$ and at most one reserved prime. When excluding 5 with $3\mid M$, discard 5, at most $k-1$ factors of $M$ above 3, and the reserved prime. In either case at most 64 primes in this list are unavailable. Removing the 64 smallest gives a lower bound, since capacity decreases with prime size. With $s_0=2^{27}-2$, put $t=\lfloor s_0/(r-2)\rfloor$. For every $s\ge s_0$, $C_r/s\ge t/((t+1)(r-2))$, by comparing $x=s/(r-2)$ with $\lfloor x\rfloor+1$. The sum of these lower bounds, rounded down term by term, exceeds $1.0118$.
* For $9\le k\le26$ when $3\mid M$ and $5\nmid M$, start at 7 and omit at most $k$ primes, including the reserved prime. The same calculation gives capacity greater than $s/3$ on each of the ranges $[9,9]$, $[10,11]$, $[12,16]$, and $[17,26]$. The weakest computed lower fraction is above $0.3880$.
* For $k\ge64$, take $y=k^2$ and $x=k^8=y^4$. Discard the at most $k+1$ unavailable primes in $(y,x]$. Their reciprocal sum is at most $(k+1)/y$. Each remaining prime contributes $C_r/s\ge1/r-1/s$. Rosser and Schoenfeld's inequalities (3.17) and (3.18) therefore give total capacity divided by $s$ greater than
  $$\log4-\frac1{(\log y)^2}-\frac{k+1}{y}-\frac{k^8}{2^k-2}>1.$$
  The three error bounds decrease for $k\ge64$ and already sum to less than $0.032$ at 64. [Rosser and Schoenfeld, Theorem 5](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)

For small $k$, the [pure-prime-power counting bound](prime-3-seeds.md) gives a direct exclusion. If $3\nmid M$ and $1\le k\le26$, it gives $h>(4/3)\tau(M)$, larger than the combined capacities even for 3 and 5. If $3\mid M$, $5\nmid M$ and $1\le k\le8$, the same bound on the prime list $3,7,11,\ldots$ gives $h>(8/15)\tau(M)$, larger than the combined capacities for 5 and 7. Each inequality is certified separately for every prime count, uniformly over exponents. The period 1 has zero repair budget. [Arithmetic certificate](h1_seed_check.py)

We can now exclude three cases.

1. If $3\nmid M$, either the repair already avoids 3 or we replace its 3-list by the preceding capacity bound. This would produce a distinct covering with every modulus coprime to 6, contradicting Hough and Nielsen. [Covering systems with restricted divisibility](https://arxiv.org/abs/1703.02133)
2. If $3\mid M$ and $5\nmid M$, replace the 5-list if present. Its capacity is only $\lfloor s/3\rfloor$. The resulting odd cover would have least common multiple coprime to 5, contrary to the divisibility-by-45 theorem of Dai, Li, Li and Yi. [On the moduli of distinct covering systems](https://arxiv.org/abs/2611.15110)
3. If $3\mid M$ but $9\nmid M$, all fresh primes differ from 3, so every repair modulus still has 3-adic exponent at most one. The same theorem excludes this case.

## At least nine primes in the starting period

Here we use Schroeder's preprint result that any odd distinct family supported on at most eight primes leaves density at least $1/1{,}002{,}375$ uncovered. A period with at most six primes would yield a full cover on at most eight after two repairs. For eight primes, $45\mid M$ implies $M/\tau(M)\ge334639305/384$ by minimizing each prime power separately. Since the two fresh primes are at least 7 and 11, the total budget is at most $(14/45)\tau(M)$. The density bound gives more holes than this. [Schroeder's preprint and verification materials](https://michaelschroeder.ai/research/NinePrimeSupport/companion)

For seven primes the same reasoning suffices whenever $M/\tau(M)>311850$. Below that cutoff the largest prime $q$ satisfies $255255q/64\le311850$, hence $q<79$. Enumerating increasing prime factors and exponents leaves 78 periods under or at the cutoff. Using the actual two smallest fresh primes removes all but two. For $M=14549535$ and $17612595$, the pure-prime-power counting bound gives at least 40545 and 168525 holes respectively, against budgets of 16 and 18. [Enumeration and checks](h1_seed_check.py)

## Excluding the entire family with a 45-coordinate and seven squarefree primes

Write $M=45\prod_{i=1}^7q_i$ for distinct primes $7\le q_1<\cdots<q_7$. By the Chinese remainder theorem we may choose coordinates independently modulo 45 and modulo each $q_i$.

Translate the chosen residues for 3 and 5 to zero. The choices for 9, 15 and 45 leave exactly $9\cdot15\cdot45=6075$ patterns to check. For every pattern the certificate provides a probability distribution $w$ supported on uncovered residues modulo 45, with
$$\max_x w(x)\le1/8,\qquad
\sum_{d\in\{3,5,9,15,45\}} \max_a\sum_{x\equiv a\pmod d}w(x)\le4/3.$$
The certificate uses 12 integer weight vectors and their invertible affine images. Linear programming located the vectors. The independent checker tests both inequalities and all 6075 patterns directly using integers. On each outer coordinate take the uniform distribution on the $q_i-1$ residues left by its pure modulus. [Weights and independent checker](h1_core45.py)

Group the remaining covering events by the coordinates they use. For a nonempty outer support $S$ put $t_S=\prod_{i\in S}1/(q_i-1)$. An outer-only event has probability at most $t_S$ and must have $|S|\ge2$. For each nonempty $S$, combine all events using $S$ and a nontrivial divisor of 45. This group has probability at most $(4/3)t_S$ by the weight inequality and the union bound. Groups on disjoint coordinates are independent, including independence from the joint family of groups on disjoint coordinates.

Use the smallest possible outer primes $7,11,13,17,19,23,29$ to upper bound all event probabilities. For any coordinate set $V$, define $Z(V)$ as the sum over collections of pairwise disjoint group supports in $V$, with a factor equal to minus its probability bound for each chosen support. The empty collection contributes one. This is the independent-set polynomial in Shearer's lemma for the dependency graph. Its values are computed by splitting on the unique chosen support containing a designated coordinate, or on there being no such support. [Scott and Sokal on Shearer's bound](https://people.maths.ox.ac.uk/scott/Papers/lllshort.pdf)

The checker verifies $Z(V)>0$ on all 256 coordinate subsets. This also suffices for arbitrary **subfamilies of events**, as required by Shearer's lemma. To see this, induct on the number of available coordinates. Deleting an event with support $E$ increases the polynomial by its weight times the polynomial of the remaining events disjoint from $E$. The latter is positive by induction on the proper coordinate subset $V\setminus E$, even when some of its events have already been deleted. Starting at the full family on $V$ proves the assertion for every subfamily.

Shearer's bound now gives avoidance probability at least $Z(\mathrm{all})=83695/4257792$. Each integer residue has probability at most $1/(8\prod_i(q_i-1))$, so the family misses **at least 20,086,800 distinct residues**. There are 768 divisors and even the most favorable two-prime budget here is at most 238. At the smallest such period, $M=9{,}704{,}539{,}845$, the available primes are 31 and 37 and the budget is 47. [Exact polynomial computed two ways](h1_core45.py)

The least period divisible by 45 with nine prime factors is $9{,}704{,}539{,}845$. Every nine-prime multiple of 45 outside the family just excluded carries at least one additional prime factor counted with multiplicity, costing a factor of at least 3 relative to that minimum. Ten distinct prime factors give an even larger minimum. This gives the stated lower bound of $29{,}113{,}619{,}535$.

## Constructive trials

For each period below we assigned a residue to **every** nontrivial divisor, using greedy selection on up to 100,000 training residues followed by two passes of coordinate ascent on small moduli. We made three assignments per period and checked each against a separate fixed set of distinct residues. Every reported hole was checked against the completed assignment. These are lower bounds on the holes in particular trial assignments. Only the first row also has the all-assignments exclusion above. [Reproducible search with NumPy](h1_seed_search.py)

| Period | One-prime budget | Two-prime budget | Distinct test residues | Fewest observed holes in three trials |
|---:|---:|---:|---:|---:|
| 9,704,539,845 | 26 | 47 | 65,536 | 3,630 |
| 29,113,619,535 | 35 | 64 | 65,537 | 2,764 |
| 145,568,097,675 | 52 | 95 | 65,537 | 1,979 |
| 3,056,930,051,175 | 99 | 181 | 65,537 | 1,466 |
