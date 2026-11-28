import OMAStatements.S_arxiv_1812_11360

-- The odd-prism switching bound of Deepak Sehrawat and Bikash Bhattacharjya.
-- See arXiv:1812.11360 and their stronger theorem in arXiv:1905.05548.
-- Formalization: @DrSubspace.

open SimpleGraph OMA.S_arxiv_1812_11360 Fin.NatCast

namespace OMA.OddPrism

private abbrev V (t : ℕ) := Fin (t + 3) × Fin 2
private abbrev E (t : ℕ) := Sym2 (V t)

private def vertex (t i : ℕ) (b : Fin 2) : V t := ((i : Fin (t + 3)), b)
private def rim (t i : ℕ) (b : Fin 2) : E t := s(vertex t i b, vertex t (i+1) b)
private def rung (t i : ℕ) : E t := s(vertex t i 0, vertex t i 1)

/-- The edges between the two induced trees: four rim edges and all but two rungs. -/
private def cut (t : ℕ) : Finset (E t) :=
  insert (rim t 0 0) (insert (rim t (t+2) 0) (insert (rim t (t+1) 1)
    (insert (rim t (t+2) 1) ((Finset.range (t+1)).image (fun j => rung t (j+1))))))

private lemma cut_bound (t : ℕ) : (cut t).card ≤ t + 5 := by
  unfold cut
  iterate 4
    apply (Finset.card_insert_le _ _).trans
    apply Nat.succ_le_succ
  simpa using Finset.card_image_le (f := fun j => rung t (j+1)) (s := Finset.range (t+1))

/-- Successive switches make the path edges positive. -/
private def pathMark {t : ℕ} (S : Set (E t)) (b : Fin 2) : ℕ → Prop
  | 0 => False
  | i+1 => (rim t i b ∉ S ↔ pathMark S b i)

/-- Side A is the top path without its first vertex, plus the final bottom vertex. -/
private def side {t : ℕ} (v : V t) : Prop :=
  if v.2 = 0 then v.1.val ≠ 0 else v.1.val = t+2

private def mark {t : ℕ} (S : Set (E t)) (v : V t) : Prop :=
  if v.2 = 0 then
    if v.1.val = 0 then (rung t 0 ∉ S ↔ pathMark S 1 0) else pathMark S 0 v.1.val
  else
    if v.1.val = t+2 then (rung t (t+2) ∉ S ↔ pathMark S 0 (t+2))
    else pathMark S 1 v.1.val

/-- Internal edges are positive under the chosen switches. Edges joining the trees lie in cut. -/
private def Good {t : ℕ} (S : Set (E t)) (u v : V t) : Prop :=
  ((side u ↔ side v) → ¬ (s(u,v) ∈ S ↔ (mark S u ↔ mark S v))) ∧
    (¬ (side u ↔ side v) → s(u,v) ∈ cut t)

private lemma good_symm {t : ℕ} {S : Set (E t)} {u v : V t} (h : Good S u v) :
    Good S v u := by
  unfold Good at *
  rw [Sym2.eq_swap]
  tauto

private lemma rung_good {t : ℕ} (S : Set (E t)) (i : ℕ) (hi : i < t+3) :
    Good S (vertex t i 0) (vertex t i 1) := by
  have hval : ((i : Fin (t+3)) : ℕ) = i := Nat.mod_eq_of_lt hi
  change ((_ ↔ _) → ¬ (rung t i ∈ S ↔ (_ ↔ _))) ∧ (¬ (_ ↔ _) → rung t i ∈ cut t)
  simp only [side, mark, vertex, hval, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
  by_cases h0 : i = 0
  · subst i
    simp
    tauto
  by_cases hl : i = t+2
  · subst i
    simp
    tauto
  · have he : rung t i ∈ cut t := by
      unfold cut
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i-1, Finset.mem_range.mpr (by omega), by congr 1; omega⟩
    simp [h0, hl, he]

private lemma rim_good {t : ℕ} (S : Set (E t)) (i : ℕ) (hi : i < t+3) (b : Fin 2) :
    Good S (vertex t i b) (vertex t (i+1) b) := by
  have hv : ((i : Fin (t+3)) : ℕ) = i := Nat.mod_eq_of_lt hi
  change ((_ ↔ _) → ¬ (rim t i b ∈ S ↔ (_ ↔ _))) ∧ (¬ (_ ↔ _) → rim t i b ∈ cut t)
  by_cases h : i = t+2
  · subst i
    have hw : (((t+2+1 : ℕ) : Fin (t+3)) : ℕ) = 0 := Nat.mod_self _
    simp only [side, vertex, hv, hw]
    fin_cases b <;> simp [cut]
  · have hw : (((i+1 : ℕ) : Fin (t+3)) : ℕ) = i+1 := Nat.mod_eq_of_lt (by omega)
    simp only [side, mark, vertex, hv, hw]
    fin_cases b
    · by_cases hz : i = 0
      · subst i
        simp [cut]
      · simp [hz, pathMark]
        tauto
    · by_cases he : i+1 = t+2
      · have hpred : i = t+1 := by omega
        subst i
        simp [cut]
      · have hpred : i ≠ t+1 := by omega
        simp [h, hpred, pathMark]
        tauto

private lemma edge_good {t : ℕ} (S : Set (E t)) {u v : V t}
    (h : (prism (t+3)).Adj u v) : Good S u v := by
  obtain ⟨i,b⟩ := u
  obtain ⟨j,c⟩ := v
  rcases boxProd_adj.mp h with ⟨ha, rfl⟩ | ⟨hb, rfl⟩
  · rcases cycleGraph_adj.mp ha with h | h
    · have he : i = j+1 := sub_eq_iff_eq_add'.mp h
      subst i
      exact good_symm (by simpa [vertex, Nat.cast_add] using rim_good S j.val j.isLt b)
    · have he : j = i+1 := sub_eq_iff_eq_add'.mp h
      subst j
      simpa [vertex, Nat.cast_add] using rim_good S i.val i.isLt b
  · have hbc : b ≠ c := hb
    have hr : Good S (i, 0) (i, 1) := by simpa [vertex] using rung_good S i.val i.isLt
    fin_cases b <;> fin_cases c <;> first | contradiction | exact hr | exact good_symm hr

private lemma membership {V : Type*} (G : SimpleGraph V) (S : Set (Sym2 V))
    (X : Set V) (u v : V) :
    s(u,v) ∈ switch G S X ↔ G.Adj u v ∧ (s(u,v) ∈ S ↔ (u ∈ X ↔ v ∈ X)) := by
  constructor
  · rintro ⟨ha, x, y, hxy, hs⟩
    refine ⟨ha, ?_⟩
    rcases Sym2.eq_iff.mp hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> tauto
  · rintro ⟨ha, hs⟩
    exact ⟨ha, u, v, rfl, hs⟩

private lemma switch_logic (a b c d p : Prop) :
    ((a ↔ b) → ¬ (p ↔ (c ↔ d))) →
    ((p ↔ (c ↔ d)) → (p ↔ ((c ↔ a) ↔ (d ↔ b))) → False) ∧
    ((p ↔ (c ↔ d)) ∨ (p ↔ ((c ↔ a) ↔ (d ↔ b))) → ¬ (a ↔ b)) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp [ha, hb, hc, hd]

private theorem bound (t : ℕ) (S : Set (E t)) :
    ∃ X : Set (V t), (switch (prism (t+3)) S X).ncard ≤ (t+5)/2 := by
  classical
  let X : Set (V t) := {u | mark S u}
  let Y : Set (V t) := {u | mark S u ↔ side u}
  let A := switch (prism (t+3)) S X
  let B := switch (prism (t+3)) S Y
  have hx (u v : V t) : s(u,v) ∈ A ↔ (prism (t+3)).Adj u v ∧
      (s(u,v) ∈ S ↔ (mark S u ↔ mark S v)) := membership _ _ _ _ _
  have hy (u v : V t) : s(u,v) ∈ B ↔ (prism (t+3)).Adj u v ∧
      (s(u,v) ∈ S ↔ ((mark S u ↔ side u) ↔ (mark S v ↔ side v))) := membership _ _ _ _ _
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    rintro ⟨u,v⟩ ha hb
    obtain ⟨adj, hp⟩ := (hx u v).mp ha
    have hq := ((hy u v).mp hb).2
    exact (switch_logic _ _ _ _ _ (edge_good S adj).1).1 hp hq
  have sub : A ∪ B ⊆ (cut t : Set (E t)) := by
    rintro ⟨u,v⟩ (ha|hb)
    · obtain ⟨adj, hp⟩ := (hx u v).mp ha
      obtain ⟨h₁,h₂⟩ := edge_good S adj
      exact h₂ ((switch_logic _ _ _ _ _ h₁).2 (Or.inl hp))
    · obtain ⟨adj, hp⟩ := (hy u v).mp hb
      obtain ⟨h₁,h₂⟩ := edge_good S adj
      exact h₂ ((switch_logic _ _ _ _ _ h₁).2 (Or.inr hp))
  have hcard := Set.ncard_le_ncard sub
  rw [Set.ncard_union_eq hd, Set.ncard_coe_finset] at hcard
  have hc := cut_bound t
  by_cases h : A.ncard ≤ (t+5)/2
  · exact ⟨X,h⟩
  · exact ⟨Y, show B.ncard ≤ (t+5)/2 by omega⟩

end OMA.OddPrism

theorem OMA.solution : type_of% @OMA.S_arxiv_1812_11360.main := by
  intro n hn
  obtain ⟨t, ht⟩ : ∃ t, 2*n+1 = t+3 := ⟨2*n-2, by omega⟩
  have hbound : (t+5)/2 = n+1 := by omega
  rw [ht]
  intro S _
  simpa only [hbound] using OMA.OddPrism.bound t S
