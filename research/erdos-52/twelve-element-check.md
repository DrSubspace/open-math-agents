# A twelve-element test for the integer sum-product problem

Antis, Britt, Chapman, Hawkins, Rice and Warren conjecture that every twelve-element set of positive integers has at least 41 different sums or at least 41 different products. They give an example with 41 sums and 35 products. We checked a two-generator family containing their example. This is a restricted finite-cardinality result. The full [Erdős problem 52](https://www.erdosproblems.com/52) asks for an asymptotic estimate across all sizes. [The sum-product problem for small sets II, section 6](https://arxiv.org/abs/2601.21828)

Let $\lambda_0\ge\cdots\ge\lambda_h>0$ sum to 12 and take any positive rational $t$. Form
$$A=\{2^i t^j:0\le j\le h,\ 0\le i<\lambda_j\}.$$
Keep the choices giving twelve distinct elements. A common dilation makes the set integral and preserves both cardinalities. For this family the minimum of $\max(|A+A|,|AA|)$ is **41**. Within the given parametrization the unique minimizing choice is $\lambda=(6,4,2)$ and $t=3$. This recovers the authors' example. No novelty claim is made for the restricted result.

## Why the parameter check is exhaustive

There are 77 possible row shapes. For each shape, treat each element as a monomial in an indeterminate $T$. Two formally different sums can coincide at a positive rational $t$ only if their difference vanishes at $t$. Remove the lowest power of $T$ and divide out the common factor of the integer coefficients. By the rational root theorem the numerator of $t$ divides the absolute constant coefficient and its denominator divides the absolute leading coefficient. Differences with all nonzero coefficients of one sign have no positive roots.

Two formally different products can coincide only if $t^b=2^a$ for integers $b\ne0$ and $|a|\le22$. A positive rational solution has the form $2^k$ for an integer $|k|\le22$, by unique factorization. These two tests give a finite superset of all exceptional ratios. At every other ratio both counts equal the formal polynomial counts.

The [standard-library Python checker](twelve_element_check.py) evaluates the generic case of each shape and 12,081 exceptional shape-and-ratio candidates, including extraneous candidates introduced by divisibility. Of these, 11,566 give twelve distinct elements. The checker clears denominators and counts sums and products with exact integers throughout. Run it with Python 3.
