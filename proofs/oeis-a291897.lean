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
