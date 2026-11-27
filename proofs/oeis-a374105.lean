import OMAStatements.S_oeis_a374105

namespace OMA.A374105

def phi (x : ℕ) : ℕ := x ^ 2 + x + 1

lemma cast_phi (m x : ℕ) :
    ((phi x : ℕ) : ZMod m) = (x : ZMod m) ^ 2 + x + 1 := by
  simp [phi]

-- Modulo phi(x), the cube of x is 1. Exponents 1 and 2 modulo 3
-- therefore both give roots of the same quadratic.
lemma phi_dvd_pow (x b : ℕ) (hb : ¬ 3 ∣ b) : phi x ∣ phi (x ^ b) := by
  let y : ZMod (phi x) := x
  have hy : y ^ 2 + y + 1 = 0 := by
    exact (cast_phi (phi x) x).symm.trans ((ZMod.natCast_eq_zero_iff _ _).2 dvd_rfl)
  have hc : y ^ 3 = 1 := by linear_combination (y - 1) * hy
  have hreduce : y ^ b = y ^ (b % 3) := by
    calc
      y ^ b = y ^ (b % 3 + 3 * (b / 3)) := congrArg (y ^ ·) (Nat.mod_add_div b 3).symm
      _ = y ^ (b % 3) := by rw [pow_add, pow_mul, hc, one_pow, mul_one]
  apply (ZMod.natCast_eq_zero_iff _ _).1
  rw [cast_phi, Nat.cast_pow]
  change (y ^ b) ^ 2 + y ^ b + 1 = 0
  rw [hreduce]
  have hr : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hr with hr | hr
  · simpa [hr] using hy
  · rw [hr]
    linear_combination (y ^ 2 - y + 1) * hy

lemma exponent_not_multiple_of_three (k : ℕ) (h : 13 ∣ phi (3 ^ k)) : ¬ 3 ∣ k := by
  rintro ⟨t, rfl⟩
  have he := (ZMod.natCast_eq_zero_iff _ _).2 h
  have hc : (3 : ZMod 13) ^ 3 = 1 := by decide
  simp only [phi, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at he
  rw [pow_mul (3 : ZMod 13) 3 t, hc, one_pow] at he
  exact (by decide : ¬ ((1 : ZMod 13) ^ 2 + 1 + 1 = 0)) he

lemma phi_strictMono : StrictMono phi := by
  intro x y hxy
  dsimp [phi]
  nlinarith [Nat.pow_le_pow_left (Nat.le_of_lt hxy) 2]

end OMA.A374105

open OMA.A374105

theorem OMA.solution : type_of% @OMA.S_oeis_a374105.main := by
  intro k p hp h
  have hpow : ((3 : ℕ) ^ k) ^ 2 = 9 ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    rfl
  have he : phi (3 ^ k) = 13 * p := by simpa only [phi, hpow] using h
  have hk3 := exponent_not_multiple_of_three k ⟨p, he⟩
  have hk : 2 ≤ k := by
    by_contra! hsmall
    interval_cases k <;> norm_num at h <;> have := hp.two_le <;> omega
  by_contra hcomp
  obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hk).1 hcomp
  have ha2 : 2 ≤ a := by
    by_contra! hsmall
    interval_cases a <;> simp_all
  have ha3 : ¬ 3 ∣ a := fun hd => hk3 (hab ▸ dvd_mul_of_dvd_left hd b)
  have hb3 : ¬ 3 ∣ b := fun hd => hk3 (hab ▸ dvd_mul_of_dvd_right hd a)
  -- The intermediate numerator lies strictly between 13 and phi(3^k).
  -- Dividing all three by 13 gives a proper divisor of p.
  obtain ⟨d, hd⟩ : 13 ∣ phi (3 ^ a) := phi_dvd_pow 3 a ha3
  have hdiv : phi (3 ^ a) ∣ phi (3 ^ k) := by
    rw [← hab, pow_mul]
    exact phi_dvd_pow _ _ hb3
  obtain ⟨c, hc⟩ := hdiv
  have hpc : p = d * c := by
    rw [hd, he, mul_assoc] at hc
    omega
  have hgrow : StrictMono (fun n : ℕ => phi (3 ^ n)) :=
    phi_strictMono.comp (pow_right_strictMono₀ (by decide : 1 < (3 : ℕ)))
  have hdlarge := hgrow (show 1 < a by omega)
  have hdsmall := hgrow ha
  change 13 < phi (3 ^ a) at hdlarge
  change phi (3 ^ a) < phi (3 ^ k) at hdsmall
  rcases hp.eq_one_or_self_of_dvd d ⟨c, hpc⟩ with hone | hself
  · omega
  · omega
