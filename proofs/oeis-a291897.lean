import OMAStatements.S_oeis_a291897

open OMA.S_oeis_a291897

namespace OMA.Shevelev

lemma odd_eulerNumber_zero {m : ℕ} (hm : m % 2 = 1) : eulerNumber m = 0 := by
  cases m with
  | zero => omega
  | succ k => rw [eulerNumber, if_pos hm]

-- Reducing a fraction with denominator 2^m preserves every odd divisor
-- of the integer numerator.
lemma dvd_reduced_num {d s : ℤ} (m : ℕ) (hc : IsCoprime d 2) (hs : d ∣ s) :
    d ∣ ((s : ℚ) / 2 ^ m).num := by
  let q := (s : ℚ) / 2 ^ m
  have hrat : (q.num : ℚ) / q.den = (s : ℚ) / 2 ^ m := q.num_div_den
  have heq : q.num * (2 : ℤ) ^ m = s * (q.den : ℤ) := by
    exact_mod_cast (div_eq_div_iff (by exact_mod_cast q.den_ne_zero) (by positivity)).mp hrat
  apply (hc.pow_right (n := m)).dvd_of_dvd_mul_right
  rw [heq]
  exact dvd_mul_of_dvd_left hs _

end OMA.Shevelev

open OMA.Shevelev

theorem OMA.solution : type_of% @OMA.S_oeis_a291897.main := by
  intro n hn
  let m := 2 * n - 1
  have hm : m % 2 = 1 := by dsimp [m]; omega
  have hx : (m : ℤ) = 2 * (n : ℤ) - 1 := by dsimp [m]; omega
  have hc : IsCoprime (2 * (n : ℤ) - 1) 2 := ⟨-1, n, by ring⟩
  apply dvd_reduced_num m hc.pow_left
  apply Finset.dvd_sum
  intro j _
  cases j with
  | zero => simp [m, odd_eulerNumber_zero hm]
  | succ j =>
    cases j with
    | zero =>
      simp only [zero_add, Nat.choose_one_right, pow_one]
      change (2 * (n : ℤ) - 1) ^ 2 ∣
        (m : ℤ) * eulerNumber (m - 1) * (2 * (n : ℤ) - 1)
      exact ⟨eulerNumber (m - 1), by rw [hx]; ring⟩
    | succ j =>
      exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega : 2 ≤ j + 2)) _

namespace OMA.Shevelev

open OMA.S_oeis_a291897

/-- The same expansion determines exactly when the numerator gains a third
factor. Here m = 2n−1, so (m+1)/2 is the argument n in Shevelev's conjecture. -/
theorem cubic_criterion (m n : ℕ) (hcenter : m + 1 = 2 * n) :
    (m : ℤ) ^ 3 ∣ (eulerValue m n).num ↔ (m : ℤ) ∣ eulerNumber (m - 1) := by
  have hm : m % 2 = 1 := by omega
  have hmpos : 0 < m := by omega
  have hx : 2 * (n : ℤ) - 1 = m := by omega
  have hc : IsCoprime (m : ℤ) 2 := ⟨-1, n, by omega⟩
  let term (j : ℕ) := (m.choose j : ℤ) * eulerNumber (m - j) * (m : ℤ) ^ j
  let inds := Finset.range (m + 1)
  let total := ∑ j ∈ inds, term j
  have hval : eulerValue m n = (total : ℚ) / 2 ^ m := by
    simp only [eulerValue, hx, total, inds, term]
  have hnum : ((m : ℤ) ^ 3 ∣ (eulerValue m n).num) ↔ (m : ℤ) ^ 3 ∣ total := by
    rw [hval]
    refine ⟨fun h => h.trans ?_, dvd_reduced_num m hc.pow_left⟩
    simpa [Rat.divInt_eq_div] using Rat.num_dvd total (b := (2 : ℤ) ^ m) (by positivity)
  have h1 : 1 ∈ inds := Finset.mem_range.mpr (by omega)
  have htail : (m : ℤ) ^ 3 ∣ ∑ j ∈ inds.erase 1, term j := by
    apply Finset.dvd_sum
    intro j hj
    obtain ⟨hj1, hjmem⟩ := Finset.mem_erase.mp hj
    have hjle := Finset.mem_range.mp hjmem
    by_cases hj0 : j = 0
    · simp [term, hj0, odd_eulerNumber_zero hm]
    by_cases hj2 : j = 2
    · have he : (m - 2) % 2 = 1 := by omega
      simp [term, hj2, odd_eulerNumber_zero he]
    exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega : 3 ≤ j)) _
  have hone : term 1 = (m : ℤ) ^ 2 * eulerNumber (m - 1) := by simp [term]; ring
  rw [hnum]
  change (m : ℤ) ^ 3 ∣ ∑ j ∈ inds, term j ↔ _
  rw [← Finset.sum_erase_add _ _ h1, dvd_add_right htail, hone, pow_succ]
  exact mul_dvd_mul_iff_left (by positivity : (m : ℤ) ^ 2 ≠ 0)

end OMA.Shevelev

/-!
For an odd prime p, the cubic criterion also answers Shevelev's follow-up
question in OEIS A292911. Zhang's congruence for Euler numbers, given as
equation (2) in Guodong Liu, *On Congruences of Euler Numbers Modulo an Odd
Square* (Fibonacci Quarterly 43, 2005), says p divides the Euler number of
index p−1 exactly when p is 1 modulo 4. Liu uses unsigned secant numbers.
Changing their signs preserves divisibility. Combining that published result
with the theorem above gives the prime case. The Lean file verifies the cubic
criterion for every odd index. The use of Zhang's congruence here is on paper.

https://oeis.org/A292911
https://www.mathstat.dal.ca/FQ/Papers1/43-2/paper43-2-7.pdf
-/
