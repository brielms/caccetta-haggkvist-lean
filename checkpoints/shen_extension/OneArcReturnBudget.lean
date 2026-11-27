import checkpoints.shen_extension.TripleBankFreeRepair

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- After deleting the unpaid leg, one row may need one arc. The return
middles with no surplus must be cut at the new head. -/
theorem one_arc_return_budget {D : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree D U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y)
    (off : D w y≠true) (back : D y w≠true)
    (need : t≤(outN D U w).card+1)
    (floor : ∀ v∈U, v≠w → t≤(outN D U v).card)
    (budget : t+((outN D U y ∩ inN D U w).filter
      (fun z => (outN D U z).card≤t)).card ≤ (outN D U y).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ ∀ i∈U, t≤(outN E U i).card := by
  classical
  let Z := outN D U y ∩ inN D U w
  let T := Z.filter (fun z => (outN D U z).card≤t)
  let A (v : ℕ) : Finset ℕ := if v=w then {y} else ∅
  let K (v : ℕ) : Finset ℕ := if v=y then T else if v∈Z ∧ v∉T then {w} else ∅
  have nw : w∉Z := fun h => back (mem_outN.mp (mem_inter.mp h).1).2
  have ny : y∉Z := fun h => back (mem_inN.mp (mem_inter.mp h).2).2
  have spec {i j} (h : j∈A i) : i=w ∧ j=y := by
    by_cases iw : i=w
    · exact ⟨iw,by simpa [A,iw] using h⟩
    · simp [A,iw] at h
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=K) safe
    (fun _ _ _ h => by obtain ⟨rfl,rfl⟩ := spec h; exact ⟨yu,wy.symm,off,back⟩)
    (fun i _ j h z zu yz zw => by
      obtain ⟨hi,hj⟩ := spec h
      subst i
      subst j
      have zm : z∈Z := mem_inter.mpr ⟨mem_outN.mpr ⟨zu,yz⟩,mem_inN.mpr ⟨zu,zw⟩⟩
      by_cases tight : z∈T
      · exact Or.inl (by simpa [K] using tight)
      · exact Or.inr (by simp [K,zm,tight,show z≠y from fun eq => ny (eq ▸ zm)]))
    (fun _ _ _ h _ g => by
      obtain ⟨rfl,rfl⟩ := spec h
      exact False.elim (wy (spec g).1.symm))
  refine ⟨_,ok,decide_eq_true (Or.inl (by simp [A] : y∈A w)),?_⟩
  intro i iu
  rw [rows i iu]
  by_cases iw : i=w
  · subst i
    simpa [A,K,wy,nw] using need
  have fl := floor i iu iw
  by_cases iy : i=y
  · subst i
    have sub : T ⊆ outN D U y := (filter_subset ..).trans inter_subset_left
    have n := card_sdiff_of_subset sub
    change t+T.card≤(outN D U y).card at budget
    simp [A,K,iw,n]
    omega
  by_cases iz : i∈Z
  · by_cases im : i∈T
    · simpa [K,iy,iz,im,A,iw] using fl
    · have hi : t < (outN D U i).card := by
        by_contra! low
        exact im (mem_filter.mpr ⟨iz,low⟩)
      have count := card_sdiff_add_card_inter (outN D U i) ({w} : Finset ℕ)
      have one := (card_le_card (inter_subset_right :
        (outN D U i ∩ {w}) ⊆ {w})).trans_eq (card_singleton _)
      simp [K,iy,iz,im,A,iw]
      omega
  · simpa [A,K,iw,iy,iz] using fl

#print axioms one_arc_return_budget
end LeanCH.BR.TripleBank
