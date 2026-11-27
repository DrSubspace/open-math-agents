import Mathlib

/-!
# Shevelev's divisibility conjecture for Euler polynomials

Vladimir Shevelev conjectured in 2017 that the reduced numerator of
the Euler polynomial of degree 2n−1 at n is divisible by (2n−1)² for n ≥ 1.

Source: https://oeis.org/A291897
Credit: @DrSubspace
-/

namespace OMA.S_oeis_a291897

/-- The signed Euler numbers, the exponential generating coefficients of
the reciprocal of cosh. Multiplying by cosh gives the even-index recurrence. -/
def eulerNumber : ℕ → ℤ
  | 0 => 1
  | m + 1 => if (m + 1) % 2 = 1 then 0 else
      -∑ j : Fin (m + 1), ((m + 1).choose j : ℤ) * eulerNumber j
termination_by m => m
decreasing_by exact j.isLt

/-- The Euler polynomial at an integer argument, using its standard expansion
around one half (NIST DLMF 24.2.10), with a common denominator of 2^m. -/
def eulerValue (m : ℕ) (x : ℤ) : ℚ :=
  ((∑ j ∈ Finset.range (m + 1),
    (m.choose j : ℤ) * eulerNumber (m - j) * (2 * x - 1) ^ j : ℤ) : ℚ) /
    2 ^ m

theorem main : ∀ n : ℕ, 0 < n →
    ((2 * (n : ℤ) - 1) ^ 2) ∣ (eulerValue (2 * n - 1) n).num := by
  sorry

end OMA.S_oeis_a291897
