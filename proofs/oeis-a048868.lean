import OMAStatements.S_oeis_a048868

open OMA.S_oeis_a048868

theorem OMA.solution : type_of% @OMA.S_oeis_a048868.main := by
  intro n hn hmajority
  by_contra h
  have hnodd : n % 2 = 1 := by
    rw [Nat.even_iff] at h
    omega
  -- Replace the prime 2 with 1 to obtain distinct odd reduced residues.
  let oddRep (p : ℕ) := if p = 2 then 1 else p
  -- Reflect those residues, then replace the exceptional even prime with 1.
  let nonprime (p : ℕ) := if n - oddRep p = 2 then 1 else n - oddRep p
  have oddRep_spec (p : ℕ) (hp : p.Prime) (hc : p.Coprime n) (hle : p ≤ n) :
      1 ≤ oddRep p ∧ oddRep p < n ∧ (oddRep p).Coprime n ∧ oddRep p % 2 = 1 := by
    have htwo := hp.two_le
    have hlt : p < n := by
      by_contra! hge
      have heq : p = n := by omega
      subst n
      simp at hc
      omega
    rcases hp.eq_two_or_odd with rfl | hodd
    · simp [oddRep]
      omega
    · have hne : p ≠ 2 := by omega
      exact ⟨by simpa [oddRep, hne] using (show 1 ≤ p by omega),
        by simpa [oddRep, hne] using hlt, by simpa [oddRep, hne] using hc,
        by simpa [oddRep, hne] using hodd⟩
  apply (Nat.not_lt_of_ge _) hmajority
  apply Finset.card_le_card_of_injOn nonprime
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, reducedResidues, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨⟨_, hle⟩, hc⟩, hprime⟩ := hp
    obtain ⟨hpos, hlt, hcop, hpar⟩ := oddRep_spec p hprime hc hle
    by_cases htwo : n - oddRep p = 2
    · simp [nonprime, htwo, Nat.not_prime_one, Nat.succ_le_of_lt hn]
    · simp only [nonprime, if_neg htwo]
      refine ⟨⟨⟨by omega, by omega⟩, (Nat.coprime_self_sub_left (by omega)).mpr hcop⟩, ?_⟩
      intro hprime'
      rcases hprime'.eq_two_or_odd with heq | hodd <;> omega
  · intro p hp q hq heq
    simp only [Finset.mem_coe, Finset.mem_filter, reducedResidues, Finset.mem_Icc] at hp hq
    obtain ⟨⟨⟨_, hple⟩, hpc⟩, hpp⟩ := hp
    obtain ⟨⟨⟨_, hqle⟩, hqc⟩, hqp⟩ := hq
    obtain ⟨_, hplt, _, hppar⟩ := oddRep_spec p hpp hpc hple
    obtain ⟨_, hqlt, _, hqpar⟩ := oddRep_spec q hqp hqc hqle
    have hsame : oddRep p = oddRep q := by
      dsimp only [nonprime] at heq
      split_ifs at heq <;> omega
    have hp2 := hpp.two_le
    have hq2 := hqp.two_le
    dsimp only [oddRep] at hsame
    split_ifs at hsame <;> omega
