import OMAStatements.S_arxiv_1804_07104

/-!
# Prime circles

Prime-sum matching by the Bertrand reflection argument of Chen, Fu and Guo
(arXiv:1804.07104), followed by a sufficient condition for a Hamilton circle.
Indices i and j denote the odd label 2i+1 and even label 2j+2.
-/
namespace PrimeCircles

abbrev Circle (n : ℕ) := ∃ a : Equiv.Perm (Fin (2*n)),
  ∀ k, ((a k).val + 1 + ((a (finRotate (2*n) k)).val + 1)).Prime

theorem catalogue_type : (∀ n, 2 ≤ n → Circle n) = type_of% @OMA.S_arxiv_1804_07104.main := rfl

/-- Reflect the upper interval and retain a smaller matching on the lower interval. -/
private def reflect {k n : ℕ} (hk : k ≤ n) (f : Fin k → Fin k) (i : Fin n) : Fin n :=
  if h : i.val < k then ⟨(f ⟨i,h⟩).val, by have := (f ⟨i,h⟩).isLt; omega⟩
  else ⟨n+k-1-i.val, by have := i.isLt; omega⟩

private lemma reflect_involutive {k n : ℕ} (hk : k ≤ n) (f : Fin k → Fin k)
    (hf : Function.Involutive f) : Function.Involutive (reflect hk f) := by
  intro i
  by_cases hi : i.val < k
  · have h := (f ⟨i.val,hi⟩).isLt
    apply Fin.ext
    simpa [reflect, hi, h] using congrArg Fin.val (hf ⟨i.val,hi⟩)
  · have h : ¬ n+k-1-i.val < k := by have := i.isLt; omega
    apply Fin.ext
    simp [reflect,hi,h]
    have := i.isLt
    omega

/-- Every even initial interval has a perfect matching with prime edge sums. -/
theorem matching (n : ℕ) :
    ∃ f : Equiv.Perm (Fin n), Function.Involutive f ∧
      ∀ i, (2 * (i.val + (f i).val) + 3).Prime := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n
      exact ⟨Equiv.refl _, fun _ => rfl, fun i => Fin.elim0 i⟩
    obtain ⟨p,hp,lo,hi⟩ := Nat.exists_prime_lt_and_le_two_mul (2*n) (by omega)
    have odd := hp.eq_two_or_odd.resolve_left (by omega)
    let k := (p-1)/2-n
    have hk : k < n := by dsimp [k]; omega
    have eqp : 2*(n+k)+1 = p := by dsimp [k]; omega
    obtain ⟨f,hf,hprime⟩ := ih k hk
    let g := reflect hk.le f
    have hg : Function.Involutive g := reflect_involutive hk.le f hf
    refine ⟨⟨g,g,hg,hg⟩,hg,?_⟩
    intro i
    change (2*(i.val+(g i).val)+3).Prime
    by_cases small : i.val < k
    · simpa [g,reflect,small] using hprime ⟨i.val,small⟩
    · have eq : 2*(i.val+(g i).val)+3 = p := by
        simp [g,reflect,small]
        have := i.isLt
        omega
      rwa [eq]

private def slot {n : ℕ} (k : Fin (2*n)) : Fin n := ⟨k.val/2, by have := k.isLt; omega⟩

private def weave {n : ℕ} (o e : Equiv.Perm (Fin n)) (k : Fin (2*n)) : Fin (2*n) :=
  if k.val%2=0 then ⟨2*(o (slot k)).val,by have := (o (slot k)).isLt; omega⟩
  else ⟨2*(e (slot k)).val+1,by have := (e (slot k)).isLt; omega⟩

private lemma weave_inj {n : ℕ} (o e : Equiv.Perm (Fin n)) : Function.Injective (weave o e) := by
  intro i j h
  have hv := congrArg Fin.val h
  by_cases hi : i.val%2=0 <;> by_cases hj : j.val%2=0 <;> simp [weave,hi,hj] at hv
  all_goals first | omega | skip
  · have he : o (slot i) = o (slot j) := Fin.ext (by omega)
    have hs := congrArg Fin.val (o.injective he)
    apply Fin.ext; change i.val/2 = j.val/2 at hs; omega
  · have he : e (slot i) = e (slot j) := Fin.ext (by omega)
    have hs := congrArg Fin.val (e.injective he)
    apply Fin.ext; change i.val/2 = j.val/2 at hs; omega

private lemma rotval {m : ℕ} (k : Fin m) :
    (finRotate m k).val = if k.val+1=m then 0 else k.val+1 := by
  cases m with
  | zero => exact Fin.elim0 k
  | succ m =>
    rw [coe_finRotate]
    have h : k = Fin.last m ↔ k.val+1 = m+1 := by simp [Fin.ext_iff]
    simp only [h]

/-- Weaving the two orders supplies the exact permutation required by the catalogue. -/
theorem from_orders {n : ℕ} (o e : Equiv.Perm (Fin n))
    (hin : ∀ i, (2*((o i).val+(e i).val)+3).Prime)
    (hout : ∀ i, (2*((o (finRotate n i)).val+(e i).val)+3).Prime) : Circle n := by
  let a := Equiv.ofBijective (weave o e) ((Finite.injective_iff_bijective).mp (weave_inj o e))
  refine ⟨a,?_⟩
  intro k
  change ((weave o e k).val+1+((weave o e (finRotate (2*n) k)).val+1)).Prime
  have hlt := k.isLt
  have hr := rotval k
  by_cases h : k.val%2=0
  · have hv : (finRotate (2*n) k).val = k.val+1 := by rw [hr]; split <;> omega
    have hs : slot (finRotate (2*n) k) = slot k := by apply Fin.ext; change _ / 2 = _ / 2; omega
    have ho : ¬ (finRotate (2*n) k).val%2=0 := by omega
    simp only [weave,if_pos h,if_neg ho,hs]
    convert hin (slot k) using 1
    ring
  · have hs : slot (finRotate (2*n) k) = finRotate n (slot k) := by
      apply Fin.ext
      rw [rotval (slot k)]
      change (finRotate (2*n) k).val/2 = if k.val/2+1=n then 0 else k.val/2+1
      split <;> split at hr <;> omega
    have ho : (finRotate (2*n) k).val%2=0 := by split at hr <;> omega
    simp only [weave,if_neg h,if_pos ho,hs]
    convert hout (slot k) using 1
    ring

/-- Taking the odd labels in increasing order and the even labels in reverse
order gives the twin-prime family of circles described in the literature. -/
theorem twin_centers {n : ℕ} (p : (2*n+1).Prime) (q : (2*n+3).Prime) : Circle n := by
  let e : Equiv.Perm (Fin n) := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  apply from_orders (Equiv.refl _) e
  · intro i
    change (2*(i.val + (Fin.rev i).val)+3).Prime
    rw [Fin.val_rev, show 2*(i.val+(n-(i.val+1)))+3 = 2*n+1 by have := i.isLt; omega]
    exact p
  · intro i
    change (2*((finRotate n i).val+(Fin.rev i).val)+3).Prime
    rw [rotval,Fin.val_rev]
    split
    · have he : n-(i.val+1) = 0 := by omega
      norm_num [he]
    · convert q using 1
      have := i.isLt
      omega

/-- Contracting the unconditional matching leaves a directed Hamilton-cycle
problem on n vertices. An order satisfying the cross-edge condition lifts. -/
theorem contracted {n : ℕ} (f o : Equiv.Perm (Fin n))
    (hm : ∀ i, (2*(i.val+(f i).val)+3).Prime)
    (hc : ∀ i, (2*((o (finRotate n i)).val + (f (o i)).val)+3).Prime) : Circle n :=
  from_orders o (o.trans f) (fun i => hm (o i)) hc

private def entry (w : List ℕ) (i : ℕ) : ℕ := w[i]?.getD 0

private def Valid (n : ℕ) (w : List ℕ) : Prop :=
  w.length = 2*n ∧ w.Nodup ∧ ∀ i : Fin (2*n),
    entry w i.val < 2*n ∧
    (entry w i.val + 1 + (entry w (if i.val+1=2*n then 0 else i.val+1) + 1)).Prime

private instance (n : ℕ) (w : List ℕ) : Decidable (Valid n w) := by unfold Valid; infer_instance

private theorem of_certificate (n : ℕ) (w : List ℕ) (h : Valid n w) : Circle n := by
  obtain ⟨hlen,hd,hw⟩ := h
  let g (k : Fin (2*n)) : Fin (2*n) := ⟨entry w k.val,(hw k).1⟩
  have hg : Function.Injective g := by
    intro i j hij
    have hi : i.val < w.length := by rw [hlen]; exact i.isLt
    have hj : j.val < w.length := by rw [hlen]; exact j.isLt
    have hv := congrArg Fin.val hij
    change entry w i.val = entry w j.val at hv
    simp only [entry,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] at hv
    apply Fin.ext
    exact (List.Nodup.getElem_inj_iff hd).mp hv
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg),?_⟩
  intro i
  change (entry w i.val+1+(entry w (finRotate (2*n) i).val+1)).Prime
  rw [rotval]
  exact (hw i).2

-- Zero-based cyclic orders from a search on the contracted graph.
private def certificates : ℕ → List ℕ
  | 2 => [0,3,2,1]
  | 3 => [0,5,4,1,2,3]
  | 4 => [0,1,2,7,4,5,6,3]
  | 5 => [0,9,2,7,4,5,6,3,8,1]
  | 6 => [0,11,6,5,4,7,10,1,2,9,8,3]
  | 7 => [0,1,2,13,4,11,6,9,8,7,10,5,12,3]
  | 8 => [0,15,2,13,4,11,6,9,8,7,10,5,12,3,14,1]
  | 9 => [0,17,4,13,2,15,6,11,10,7,8,9,12,5,16,1,14,3]
  | 10 => [0,1,2,19,8,13,14,7,4,17,10,11,16,5,6,15,12,9,18,3]
  | 11 => [0,21,6,15,2,19,8,13,4,17,10,11,16,5,12,9,18,3,14,7,20,1]
  | 12 => [0,3,6,21,18,9,12,15,14,13,2,1,8,19,20,7,4,23,16,11,10,17,22,5]
  | 13 => [0,1,2,25,14,13,8,19,20,7,4,23,16,11,10,17,22,5,6,21,18,9,12,15,24,3]
  | 14 => [0,27,2,25,4,23,16,11,10,17,22,5,6,21,18,9,12,15,24,3,8,19,20,7,14,13,26,1]
  | 15 => [0,29,6,23,18,11,24,5,12,17,4,25,10,19,22,7,28,1,16,13,2,27,8,21,20,9,26,3,14,15]
  | 16 => [0,3,6,29,12,23,18,17,24,11,30,5,4,31,8,27,14,21,20,15,2,1,28,7,10,25,16,19,22,13,26,9]
  | 17 => [0,1,4,31,10,25,14,21,18,17,12,23,6,29,30,5,24,11,28,7,22,13,16,19,8,27,2,33,32,3,26,9,20,15]
  | 18 => [0,35,6,29,12,23,18,17,24,11,30,5,4,31,10,25,16,19,22,13,28,7,34,1,14,21,8,27,2,33,32,3,26,9,20,15]
  | 19 => [0,1,8,31,20,19,2,37,14,25,26,13,32,7,10,29,22,17,4,35,16,23,28,11,34,5,12,27,24,15,6,33,36,3,18,21,30,9]
  | 20 => [0,39,2,37,14,25,10,29,12,27,24,15,6,33,18,21,36,3,8,31,4,35,22,17,34,5,16,23,28,11,30,9,26,13,32,7,20,19,38,1]
  | 21 => [0,41,18,23,6,35,24,17,12,29,30,11,4,37,2,39,26,15,14,27,8,33,32,9,20,21,38,3,36,5,10,31,28,13,16,25,34,7,22,19,40,1]
  | 22 => [0,1,2,43,8,37,32,13,26,19,20,25,14,31,38,7,4,41,10,35,34,11,28,17,22,23,16,29,40,5,6,39,12,33,18,27,24,21,30,15,36,9,42,3]
  | 23 => [0,45,6,39,2,43,16,29,10,35,4,41,40,5,34,11,28,17,22,23,12,33,36,9,30,15,24,21,18,27,42,3,8,37,14,31,20,25,26,19,32,13,38,7,44,1]
  | 24 => [0,3,6,45,12,39,18,33,24,27,30,21,36,15,42,9,8,43,14,37,20,31,26,25,32,19,38,13,44,7,2,1,4,47,10,41,16,35,22,29,28,23,34,17,40,11,46,5]
  | 25 => [0,1,2,49,8,43,14,37,20,31,26,25,32,19,38,13,44,7,4,47,10,41,16,35,22,29,28,23,34,17,40,11,46,5,6,45,12,39,18,33,24,27,30,21,36,15,42,9,48,3]
  | 26 => [0,51,6,45,12,39,18,33,8,43,22,29,28,23,4,47,34,17,10,41,16,35,46,5,40,11,24,27,30,21,36,15,42,9,48,3,2,49,20,31,14,37,32,19,38,13,26,25,44,7,50,1]
  | 27 => [0,3,12,45,6,51,18,39,30,27,24,33,36,21,48,9,42,15,14,43,26,31,20,37,32,25,44,13,2,1,8,49,38,19,50,7,4,53,16,41,10,47,22,35,34,23,28,29,40,17,52,5,46,11]
  | 28 => [0,1,14,43,16,41,18,39,6,51,36,21,24,33,12,45,42,15,54,3,48,9,30,27,2,55,32,25,20,37,8,49,38,19,26,31,50,7,44,13,4,53,34,23,22,35,10,47,40,17,28,29,52,5,46,11]
  | 29 => [0,57,12,45,14,43,16,41,28,29,10,47,4,53,34,23,22,35,46,11,40,17,52,5,30,27,18,39,6,51,36,21,24,33,48,9,42,15,54,3,2,55,32,25,20,37,8,49,38,19,50,7,44,13,26,31,56,1]
  | 30 => [0,59,18,41,24,35,42,17,12,47,30,29,6,53,48,11,54,5,36,23,16,43,22,37,4,55,10,49,28,31,34,25,52,7,58,1,40,19,46,13,14,45,20,39,2,57,44,15,26,33,8,51,50,9,32,27,38,21,56,3]
  | 31 => [0,3,6,59,36,29,30,35,24,41,60,5,54,11,18,47,12,53,42,23,48,17,4,61,20,45,26,39,32,33,8,57,14,51,56,9,50,15,2,1,28,37,34,31,40,25,10,55,16,49,22,43,58,7,52,13,46,19,38,27,44,21]
  | 32 => [0,1,4,61,34,31,28,37,22,43,52,13,58,7,10,55,16,49,46,19,40,25,2,63,8,57,38,27,32,33,26,39,62,3,56,9,20,45,14,51,44,21,50,15,6,59,36,29,30,35,24,41,60,5,54,11,18,47,12,53,42,23,48,17]
  | _ => []

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem through_32 (n : ℕ) (lo : 2 ≤ n) (hi : n ≤ 32) : Circle n := by
  apply of_certificate n (certificates n)
  interval_cases n <;> decide

/-- Zero-based labels on the initial interval; distinct vertices are joined when
their positive labels have prime sum. -/
def graph (N : ℕ) : SimpleGraph (Fin N) where
  Adj i j := i ≠ j ∧ (i.val+j.val+2).Prime
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa only [Nat.add_comm j.val i.val] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The undirected host has a spanning tree: every vertex except label 1
has an edge to a strictly smaller positive label. -/
theorem descends {N : ℕ} (i : Fin N) (hi : 0 < i.val) :
    ∃ j : Fin N, j.val < i.val ∧ (graph N).Adj i j := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (i.val+1) (by omega)
  have hodd := hp.eq_two_or_odd.resolve_left (by omega)
  let j : Fin N := ⟨p-i.val-2,by have := i.isLt; omega⟩
  have hj : j.val < i.val := by dsimp [j]; omega
  refine ⟨j,hj,?_,?_⟩
  · intro h; have := congrArg Fin.val h; omega
  · change (i.val+(p-i.val-2)+2).Prime
    rwa [show i.val+(p-i.val-2)+2=p by omega]

theorem graph_connected (N : ℕ) [NeZero N] : (graph N).Connected := by
  have reach (i : Fin N) : (graph N).Reachable i 0 := by
    induction i using (measure (fun x : Fin N => x.val)).wf.induction with
    | h i ih =>
      by_cases hz : i.val = 0
      · have he : i = 0 := Fin.ext hz
        subst i; exact .refl _
      · obtain ⟨j,hj,edge⟩ := descends i (by omega)
        exact edge.reachable.trans (ih j hj)
  exact ⟨fun i j => (reach i).trans (reach j).symm⟩

end PrimeCircles

