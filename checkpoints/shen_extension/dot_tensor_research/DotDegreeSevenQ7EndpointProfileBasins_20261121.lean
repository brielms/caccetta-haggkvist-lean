import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileTraits_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

def IsSinkOn (D : CH.Digraph) (A : Finset ℕ) (s : ℕ) : Prop :=
  s ∈ A ∧ ∀ z ∈ A, D s z ≠ true

def ExclusiveBasin (D : CH.Digraph) (A : Finset ℕ) (s x : ℕ) : Prop :=
  x ∈ A ∧ ∀ t, IsSinkOn D A t → (∃ m, Walk D A x t m) → t = s

/-- With two sinks on seven labels, no shortest sink path can use all seven labels. -/
theorem sink_path_le_five {D : CH.Digraph} {A : Finset ℕ} {x : ℕ}
    (hf : QFree D A 7) (ac : A.card=7)
    (two : ∃ s t, IsSinkOn D A s ∧ IsSinkOn D A t ∧ s ≠ t)
    (p : ShortestSinkPath D A x) : p.len ≤ 5 := by
  classical
  by_contra! long
  have len : p.len=6 := by have h := p.bounded; omega
  have inj := p.injective hf (by omega)
  have eq : (range (p.len+1)).image p.vertex = A := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact p.mem _ (by have := mem_range.mp hi; omega)
    · rw [card_image_of_injOn inj,card_range]
      omega
  have allsink (s) (hs : IsSinkOn D A s) : s=p.vertex p.len := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (eq.symm ▸ hs.1)
    have le := mem_range.mp hi
    by_cases h : i=p.len
    · rw [h]
    · exact (hs.2 _ (p.mem _ (by omega)) (p.edge i (by omega))).elim
  obtain ⟨s,t,hs,ht,ne⟩ := two
  exact ne ((allsink s hs).trans (allsink t ht).symm)

/-- A vertex in an exclusive basin carries its entire internal path to the sink in that basin. -/
theorem exclusive_of_walk {D : CH.Digraph} {A : Finset ℕ} {s x y m : ℕ}
    (h : ExclusiveBasin D A s x) (hy : y∈A) (w : Walk D A x y m) :
    ExclusiveBasin D A s y :=
  ⟨hy,fun t ht ⟨n,z⟩ => h.2 t ht ⟨m+n,w.append z⟩⟩

theorem exclusive_ne {D : CH.Digraph} {A : Finset ℕ} {s t x : ℕ}
    (hf : QFree D A 7) (ac : A.card≤7) (ne : s≠t)
    (hs : ExclusiveBasin D A s x) (ht : ExclusiveBasin D A t x) : False := by
  obtain ⟨z,hz,sink,m,_,w⟩ := reach_sink_of_card hf ac hs.1
  exact ne ((hs.2 z ⟨hz,sink⟩ ⟨m,w⟩).symm.trans (ht.2 z ⟨hz,sink⟩ ⟨m,w⟩))

/-- The simultaneous return tensor on two distinct active basins forces a length budget. -/
theorem basin_pair_gap {D : CH.Digraph} {V A : Finset ℕ} {s t x y bs bt i j : ℕ}
    (hf : QFree D V 7) (sub : A⊆V) (hx : x∈A) (hy : y∈A)
    (hbs : bs∈V) (hbt : bt∈V)
    (ws : Walk D A x s i) (wt : Walk D A y t j)
    (est : D s bt=true) (ety : D bt y=true)
    (ets : D t bs=true) (esx : D bs x=true) : 4≤i+j := by
  by_contra! low
  have loop := ((((((ws.mono sub).snoc hbt est).snoc (sub hy) ety).append
    (wt.mono sub)).snoc hbs ets).snoc (sub hx) esx)
  exact hf x _ (by omega) (by omega) loop

/-- Every sink reachable by a path short enough to close through a return arc must missing its B-parent. -/
theorem returns_to_sink_omitted {D : CH.Digraph} {V A : Finset ℕ} {s x b m : ℕ}
    (hf : QFree D V 7) (sub : A⊆V) (hx : x∈A) (hb : b∈V)
    (w : Walk D A x s m) (short : m≤5) (back : D b x=true) : D s b≠true := by
  intro arc
  exact hf x (m+1+1) (by omega) (by omega) (((w.mono sub).snoc hb arc).snoc (sub hx) back)

#print axioms sink_path_le_five
#print axioms exclusive_of_walk
#print axioms exclusive_ne
#print axioms basin_pair_gap
#print axioms returns_to_sink_omitted

/-- On seven acyclic labels, a walk into any specified sink has length at most
five when there is another sink. This does not replace that sink by the closest. -/
theorem walk_to_sink_le_five {D : CH.Digraph} {A : Finset ℕ} {x t m : ℕ}
    (hf : QFree D A 7) (ac : A.card=7) (hx : x∈A)
    (_st : IsSinkOn D A t) (other : ∃ s, IsSinkOn D A s ∧ s≠t)
    (w : Walk D A x t m) : m≤5 := by
  classical
  obtain ⟨f,f0,fm,edge⟩ := w.toFun
  have mem (i) (hi : i≤m) : f i∈A := by
    by_cases h : i=0
    · simpa [h,f0] using hx
    · simpa only [Nat.sub_add_cancel (show 1≤i by omega)] using (edge (i-1) (by omega)).1
  have inj (l) (lm : l≤m) (l7 : l≤7) : Set.InjOn f (range (l+1)) := by
    intro i hi j hj eq
    have hi := mem_range.mp hi
    have hj := mem_range.mp hj
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with ij | ji
    · have w' := walk_between edge ij.le (show j≤m by omega)
      rw [←eq] at w'
      exact hf (f i) (j-i) (by omega) (by omega) w'
    · have w' := walk_between edge ji.le (show i≤m by omega)
      rw [eq] at w'
      exact hf (f j) (i-j) (by omega) (by omega) w'
  have sub (l) (lm : l≤m) : (range (l+1)).image f ⊆ A := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    exact mem i (by have := mem_range.mp hi; omega)
  have mle : m≤6 := by
    by_contra! ml
    have c := card_le_card (sub 7 ml)
    rw [card_image_of_injOn (inj 7 ml le_rfl),card_range,ac] at c
    omega
  by_contra! ml
  have eq := eq_of_subset_of_card_le (sub m le_rfl) (by
    rw [card_image_of_injOn (inj m le_rfl (by omega)),card_range,ac]
    omega)
  obtain ⟨s,ss,ne⟩ := other
  obtain ⟨i,hi,fi⟩ := mem_image.mp (eq.symm ▸ ss.1)
  have hi := mem_range.mp hi
  have il : i<m := by
    by_contra! h
    have e : i=m := by omega
    exact ne (fi.symm.trans (e ▸ fm))
  exact ss.2 _ (edge i il).1 (fi ▸ (edge i il).2)

/-- If distinct sinks missing distinct B-labels, a B-return has exactly one
possible reachable sink, keeping the actual return label and basin together. -/
theorem return_classified {D : CH.Digraph} {V A B : Finset ℕ} {x b : ℕ}
    (hf : QFree D V 7) (sub : A⊆V) (ac : A.card=7) (bV : B⊆V)
    (two : ∀ s, IsSinkOn D A s → ∃ t, IsSinkOn D A t ∧ t≠s)
    (missing : ℕ→ℕ)
    (omit_inj : ∀ s, IsSinkOn D A s → ∀ t, IsSinkOn D A t → missing s=missing t → s=t)
    (omitted : ∀ s, IsSinkOn D A s → ∀ y∈B, (D s y≠true ↔ y=missing s))
    (hx : x∈A) (hb : b∈B) (back : D b x=true) :
    ∃ s, IsSinkOn D A s ∧ b=missing s ∧ ExclusiveBasin D A s x := by
  obtain ⟨s,hs,ss,m,_,w⟩ := reach_sink_of_card (hf.mono_set sub) (by omega) hx
  have hs' : IsSinkOn D A s := ⟨hs,ss⟩
  have any (t) (ht : IsSinkOn D A t) (k) (wt : Walk D A x t k) : b=missing t :=
    (omitted t ht b hb).mp
      (returns_to_sink_omitted hf sub hx (bV hb) wt
        (walk_to_sink_le_five (hf.mono_set sub) ac hx ht (two t ht) wt) back)
  exact ⟨s,hs',any s hs' m w,⟨hx,fun t ht ⟨k,wt⟩ =>
    omit_inj t ht s hs' ((any t ht k wt).symm.trans (any s hs' m w))⟩⟩

#print axioms walk_to_sink_le_five
#print axioms return_classified

end LeanCH.BR.DotDegreeSevenQ7


