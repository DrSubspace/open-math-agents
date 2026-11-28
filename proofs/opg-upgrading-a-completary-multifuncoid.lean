import OMAStatements.S_opg_upgrading_a_completary_multifuncoid

-- Victor Porton's conjecture on upgrading a completary multifuncoid.
-- Independent counterexample formalized by @DrSubspace.

open Filter OMA.S_opg_upgrading_a_completary_multifuncoid

namespace OMA.PortonCounterexample

/-- Coordinate zero stores the number. The remaining coordinates mark its index. -/
private def row (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => if i = n then 1 else 0

/-- The box meets at least one of the rows. -/
private def boxes : Set (ℕ → Set ℕ) := {Y | ∃ n, ∀ i, row n i ∈ Y i}

private lemma boxes_completary : IsCompletaryP boxes := by
  classical
  constructor
  · intro L R
    constructor
    · rintro ⟨n, h⟩
      refine ⟨fun i => decide (row n i ∈ R i), n, fun i => ?_⟩
      by_cases hr : row n i ∈ R i
      · simp [hr]
      · simpa [hr] using (h i).resolve_right hr
    · rintro ⟨c, n, h⟩
      refine ⟨n, fun i => ?_⟩
      have hi := h i
      cases hc : c i
      · exact Or.inl (by simpa [hc] using hi)
      · exact Or.inr (by simpa [hc] using hi)
  · rintro L ⟨i, hi⟩ ⟨n, hn⟩
    simpa [hi] using hn i

private def side (bit : ℕ) : ℕ → Filter ℕ
  | 0 => atTop
  | _ + 1 => pure bit

private lemma mixed_mem :
    (fun i => side 0 i ⊔ side 1 i) ∈ upgrade boxes := by
  intro Y h
  have h0 : Y 0 ∈ (atTop : Filter ℕ) := by
    simpa [side] using le_principal_iff.mp (h 0)
  obtain ⟨n, hn⟩ := mem_atTop_sets.mp h0
  refine ⟨n, ?_⟩
  intro i
  cases i with
  | zero => exact hn n le_rfl
  | succ i =>
    obtain ⟨hz, ho⟩ := sup_le_iff.mp (h (i + 1))
    by_cases he : i = n
    · simpa [row, he, side] using le_principal_iff.mp ho
    · simpa [row, he, side] using le_principal_iff.mp hz

/-- A fixed selection would realize the same marker sequence at arbitrarily large indices. -/
private lemma no_selection (c : ℕ → Bool) :
    (fun i => if c i then side 1 i else side 0 i) ∉ upgrade boxes := by
  intro h
  let bit (i : ℕ) : ℕ := if c (i + 1) then 1 else 0
  have unbounded (d : ℕ) : ∃ n, d ≤ n ∧ ∀ i, row n (i + 1) = bit i := by
    let Y : ℕ → Set ℕ := fun j => match j with
      | 0 => Set.Ici d
      | i + 1 => {bit i}
    have hy : Y ∈ boxes := h Y (by
      intro j
      cases j with
      | zero => simpa [side, Y, le_principal_iff] using (Ici_mem_atTop d)
      | succ i =>
        cases hc : c (i + 1) <;> simp [hc, side, Y, bit])
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, hn 0, fun i => hn (i + 1)⟩
  obtain ⟨n, _, h₁⟩ := unbounded 0
  obtain ⟨m, hm, h₂⟩ := unbounded (n + 1)
  have hne : n ≠ m := by omega
  have he := (h₁ n).trans (h₂ n).symm
  simp [row, hne] at he

end OMA.PortonCounterexample

open OMA.PortonCounterexample in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_upgrading_a_completary_multifuncoid.main) := by
  intro h
  obtain ⟨c, hc⟩ := ((h ℕ ℕ boxes boxes_completary).1 (side 0) (side 1)).mp mixed_mem
  exact no_selection c hc
