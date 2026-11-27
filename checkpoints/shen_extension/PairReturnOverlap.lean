import checkpoints.shen_extension.CriticalReturnPool

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- At the two-label order both marked bank labels are heads of x. No
bank label can point to w. Inside the predecessors of w, pair coverage
produces h→r→p. Neither h nor r can be a successor of p. -/
theorem pair_return_overlap_four {D : CH.Digraph} {V B : Finset ℕ} {t p w x : ℕ}
    (safe : QFree D V 3) (reg : OutEq (t+1) D V) (pos : 1≤t)
    (order : V.card=3*t+2) (no : BypassRepair.NoHost 3 t) (bv : B⊆V) (two : B.card=2)
    (pu : p∈V\B) (wu : w∈V\B) (xu : x∈V\B) (target : ∀ b∈B, D b p=true)
    (pw : D p w=true) (wx : D w x=true) (hit : (outN D B x).card=2) :
    4≤returnOverlap D (V\B) p w x := by
  classical
  let U := V\B
  have uv : U⊆V := sdiff_subset
  have size : U.card=3*t := by change (V\B).card=_; rw [card_sdiff_of_subset bv,two,order]; omega
  have allB : outN D B x=B := eq_of_subset_of_card_le outN_subset (by omega)
  have inU {a} (av : a∈V) (aw : D a w=true) : a∈U := by
    refine mem_sdiff.mpr ⟨av,fun ab => ?_⟩
    have xa := (mem_outN.mp (show a∈outN D B x by rw [allB]; exact ab)).2
    exact safe w 3 (by decide) (by decide) (.step (uv xu) wx (.step av xa (.step (uv wu) aw (.refl _))))
  have pred {a} (av : a∈V) (aw : a≠w) : ∃ r∈U, D r a=true ∧ D r w=true := by
    obtain ⟨r,rv,ra,rw⟩ := JointFreeTargets.pair_covered (s:=t+1) safe reg (by omega) av (uv wu) aw
      (by simpa using order) (by simpa using no)
    have rw' := (mem_outN.mp (mem_filter.mp rw).1).2
    exact ⟨r,inU rv rw',(mem_outN.mp (mem_filter.mp ra).1).2,rw'⟩
  have pwe : p≠w := fun e => loopfree safe (by decide) (uv wu) (e ▸ pw)
  obtain ⟨r,ru,rp,rw⟩ := pred (uv pu) pwe
  obtain ⟨h,hu,hr,hw⟩ := pred (uv ru) (fun e => loopfree safe (by decide) (uv wu) (e ▸ rw))
  have hr' : h≠r := fun e => loopfree safe (by decide) (uv ru) (e ▸ hr)
  have rnp : D p r≠true := digonfree safe (by decide) (uv ru) (uv pu) rp
  have hnp : D p h≠true := fun ph => safe p 3 (by decide) (by decide)
    (.step (uv hu) ph (.step (uv ru) hr (.step (uv pu) rp (.refl _))))
  let F := ((inN D U w).erase p) \ outN D U p
  have incl : ({h,r} : Finset ℕ) ⊆ F := by
    apply insert_subset
    · exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun e => rnp (e ▸ hr),mem_inN.mpr ⟨hu,hw⟩⟩,
        fun m => hnp (mem_outN.mp m).2⟩
    · exact singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_erase.mpr
        ⟨fun e => loopfree safe (by decide) (uv pu) (e ▸ rp),mem_inN.mpr ⟨ru,rw⟩⟩,
        fun m => rnp (mem_outN.mp m).2⟩)
  have left := card_le_card incl
  rw [card_pair hr'] at left
  have split (a) (au : a∈U) : (outN D B a).card+(outN D U a).card=t+1 := by
    have h := card_outN_union (D:=D) (show Disjoint B U from disjoint_sdiff) a
    rw [union_sdiff_of_subset bv,reg a (uv au)] at h
    omega
  have full {a} (au : a∈U) (off : ∀ b∈B, D a b≠true) : (outN D U a).card=t+1 := by
    have empty : outN D B a=∅ := eq_empty_iff_forall_notMem.mpr
      (fun b m => off b (outN_subset m) (mem_outN.mp m).2)
    simpa [empty] using split a au
  have np := full pu (fun b bb => digonfree safe (by decide) (bv bb) (uv pu) (target b bb))
  have nw := full wu (fun b bb wb => safe b 3 (by decide) (by decide)
    (.step (uv pu) (target b bb) (.step (uv wu) pw (.step (bv bb) wb (.refl _)))))
  have nx := split x xu
  have result := return_predecessor_budget (safe.mono_set uv) pu wu xu pw wx size np nw (by omega)
  change F.card+2 ≤ _ at result
  change 4≤returnOverlap D U p w x
  omega

#print axioms pair_return_overlap_four
end LeanCH.BR.TripleBank
