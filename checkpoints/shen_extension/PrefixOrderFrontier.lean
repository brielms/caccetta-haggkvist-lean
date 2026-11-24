import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightNarrowed_20261121

namespace LeanCH.BR.PrefixFrontier
open Finset BRq3 CHRuleCatalog

/-- The same physical labels and arcs give a CH child at any affordable smaller
order and degree when its cycle-length quota suffices at the parent. -/
theorem prefix_child (p : Input) (bad : Bad p) {m d} (pos : 0<m) (degree : 0<d)
    (within : m≤p.n) (loss : d+(p.n-m)≤p.s) (quota : CH.ceilDiv m d≤cutoff p) :
    Child p ⟨m,d,p.D⟩ := by
  classical
  refine ⟨pos,degree,fun i hi=>bad.loopless i (hi.trans_le within),?_,?_⟩
  · intro i hi
    let A := outN p.D (range p.n) i
    let B := outN p.D (range m) i
    have sub : B⊆A := fun j hj=>mem_outN.mpr ⟨range_mono within (mem_outN.mp hj).1,(mem_outN.mp hj).2⟩
    have deleted : A\B⊆range p.n\range m := by
      intro j hj
      obtain ⟨ja,off⟩ := mem_sdiff.mp hj
      exact mem_sdiff.mpr ⟨(mem_outN.mp ja).1,fun h=>off (mem_outN.mpr ⟨h,(mem_outN.mp ja).2⟩)⟩
    have cap := card_le_card deleted
    rw [card_sdiff_of_subset (range_mono within),card_range,card_range] at cap
    have total := card_sdiff_add_card_eq_card sub
    have orig : p.s≤A.card := Compose.FloorSix.out_card bad.degree (hi.trans_le within)
    obtain ⟨S,inside,sz⟩ := exists_subset_card_eq (show d≤B.card by omega)
    exact ⟨S.toList,by simpa using sz,S.nodup_toList,fun j hj=>
      ⟨mem_range.mp (mem_outN.mp (inside (mem_toList.mp hj))).1,(mem_outN.mp (inside (mem_toList.mp hj))).2⟩⟩
  · rintro ⟨L,cycle,len⟩
    cases L with
    | nil => exact cycle.elim
    | cons h t =>
      exact ⟨h::t,⟨cycle.1,cycle.2.1,fun j hj=>(cycle.2.2.1 j hj).trans_le within,cycle.2.2.2⟩,
        len.trans quota⟩

/-- All affordable lower-degree orders must satisfy the supplied frontier. -/
theorem all_orders (p : Input) (bad : Bad p) {d : ℕ} (hd : 0<d) {R : ℕ→ℕ→Prop}
    (frontier : ∀m D, Bad ⟨m,d,D⟩ → R m (CH.ceilDiv m d)) :
    ∀m,0<m → m≤p.n → d+(p.n-m)≤p.s → CH.ceilDiv m d≤cutoff p → R m (CH.ceilDiv m d) :=
  fun m pos sub loss cut=>frontier m p.D (bad_child bad (prefix_child p bad pos hd sub loss cut))

theorem eight_orders (p : Input) (bad : Bad p) :
    ∀m,0<m → m≤p.n → 8+(p.n-m)≤p.s → CH.ceilDiv m 8≤cutoff p →
      DotDegreeEight.Narrowed m (CH.ceilDiv m 8) :=
  all_orders p bad (by decide) (fun _ _ b=>DotDegreeEight.narrowed_eight b)

/-- Literal root-cycle consumer. The data are entirely arithmetic. -/
def Gate (n r q : ℕ) := ∃m,0<m ∧ m≤n ∧ 8+(n-m)≤r ∧ CH.ceilDiv m 8≤q ∧
  ¬DotDegreeEight.Narrowed m (CH.ceilDiv m 8)

theorem close {n r D} (hn : 0<n) (hr : 0<r) (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (gate : Gate n r (CH.ceilDiv n r)) : CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra miss
  let p : Input := ⟨n,r,D⟩
  have bad : Bad p := ⟨hn,hr,loop,degree,miss⟩
  obtain ⟨m,mp,within,loss,cut,off⟩ := gate
  exact off (eight_orders p bad m mp within loss cut)

theorem at_51 : Gate 51 8 (CH.ceilDiv 51 8) := by
  refine ⟨51,by decide,by decide,by decide,by decide,?_⟩
  unfold DotDegreeEight.Narrowed CH.ceilDiv
  omega

theorem at_64_nine : Gate 64 9 (CH.ceilDiv 64 9) := by
  refine ⟨63,by decide,by decide,by decide,by decide,?_⟩
  unfold DotDegreeEight.Narrowed CH.ceilDiv
  omega

theorem cycle_51 (D : CH.Digraph) (loop : CH.Loopless D 51) (degree : CH.MinOutdegreeAtLeast D 51 8) :
    CH.HasDirectedCycleAtMost D 51 7 := close (by decide) (by decide) loop degree at_51

theorem cycle_64_nine (D : CH.Digraph) (loop : CH.Loopless D 64) (degree : CH.MinOutdegreeAtLeast D 64 9) :
    CH.HasDirectedCycleAtMost D 64 8 := close (by decide) (by decide) loop degree at_64_nine

#print axioms cycle_51
#print axioms cycle_64_nine
#print axioms prefix_child
#print axioms all_orders
#print axioms eight_orders
#print axioms close
#print axioms at_51
#print axioms at_64_nine
end LeanCH.BR.PrefixFrontier
