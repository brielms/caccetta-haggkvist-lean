import checkpoints.shen_extension.CommonHeadLastCut

namespace LeanCH.BR.CommonHeadLastCut
open Finset BRq2 BRq3 BR45 FundedCascade BypassRepair BypassBankReplay JointShortcut
open scoped Classical

private theorem tail_spare {D V q s p h} (free : QFree D V q)
    (reg : OutEq s D V) (pv : p∈V) (hv : h∈V) {z y k}
    (common : z∈heads D V p h) (yu : y∈V \ {p,h})
    (path : Walk D (V \ {p,h}) z y k) (length : k+2≤q) : (outN D (V \ {p,h}) y).card=s := by
  have skip (a) (av : a∈V) (az : D a z=true) : D y a≠true := by
    intro ya
    have w : Walk D V a a ((k+1)+1) := .step (outN_subset (mem_inter.mp common).1) az
      ((path.mono sdiff_subset).snoc av ya)
    exact free a _ (by omega) (by omega) w
  have np := skip p pv (mem_outN.mp (mem_inter.mp common).1).2
  have nh := skip h hv (mem_outN.mp (mem_inter.mp common).2).2
  have eq : outN D (V \ {p,h}) y=outN D V y := by
    ext x
    simp only [mem_outN,mem_sdiff,mem_insert,mem_singleton]
    grind
  rw [eq,reg _ (mem_sdiff.mp yu).1]

noncomputable def previousBill (D : CH.Digraph) (U S : Finset ℕ) (q : ℕ) (f : ℕ → ℕ)
    (b : ℕ) : Finset ℕ := by
  classical
  exact U.filter (fun y => D b y=true ∧ 2≤(bill D U S q f y).card ∧
    ∃ u∈S, D y u=true ∧ Walk D U (f u) b (q-3))

/-- Unless an actual earlier tail owes arcs to two distinct contested
last payers, two disjoint layers of affordable cuts clear all selected offers. -/
theorem fork {D V q s p h} (free : QFree D V q) (hq : 3≤q) (reg : OutEq s D V)
    (hs : 2≤s) (pv : p∈V) (hv : h∈V) (ph : p≠h) (bank : Eligible V {p,h} q (s-1))
    (none : NoHost q (s-1)) (f : ℕ → ℕ)
    (choose : ∀ u∈jointParents D V p h, f u∈heads D V p h ∧ D u (f u)≠true) :
    let U := V \ {p,h}
    let S := jointParents D V p h
    ∃ b∈U,(outN D U b).card=s ∧ 2≤(previousBill D U S q f b).card := by
  classical
  let U := V \ {p,h}
  let S := jointParents D V p h
  let L := bill D U S q f
  let K := previousBill D U S q f
  let C := fun y => if (K y).Nonempty then K y else if (L y).card≤1 then L y else ∅
  have fullK (y) (yu : y∈U) (active : (K y).Nonempty) : (outN D U y).card=s := by
    obtain ⟨z,zm⟩ := active
    obtain ⟨_,_,_,u,us,_,w⟩ := mem_filter.mp zm
    exact tail_spare free reg pv hv (choose _ us).1 yu w (by omega)
  have separate (y) (active : (K y).Nonempty) (u) (us : u∈S) : D y u≠true := by
    intro yu
    obtain ⟨z,zm⟩ := active
    obtain ⟨_,_,_,a,as',_,w⟩ := mem_filter.mp zm
    have pp := (mem_outN.mp (mem_inter.mp (choose a as').1).1).2
    have chord : Walk D V p p (((q-3+1)+1)+1) := .step (outN_subset (mem_inter.mp (choose _ as').1).1) pp
      (((w.mono sdiff_subset).snoc (parent_data us).1 yu).snoc pv (parent_data us).2.1)
    exact free p _ (by omega) (by omega) chord
  by_contra noFork
  have budget (y) (yu : y∈U) : (C y).card≤spare D U (s-1) y := by
    by_cases active : (K y).Nonempty
    · have rich := fullK y yu active
      have cap : (K y).card≤1 := by
        by_contra! big
        exact noFork ⟨y,yu,rich,big⟩
      rw [show C y=K y from ite_eq_left active]
      simp only [spare,rich]
      omega
    · by_cases low : (L y).card≤1
      · by_cases haveL : (L y).Nonempty
        · obtain ⟨u,um⟩ := haveL
          obtain ⟨us,_,w⟩ := mem_filter.mp um
          have rich := tail_spare free reg pv hv (choose _ us).1 yu w (by omega)
          simp only [C,ite_eq_right active,ite_eq_left low,spare]
          change (L y).card≤(outN D U y).card-(s-1)
          change (outN D U y).card=s at rich
          omega
        · simp [C,active,not_nonempty_iff_eq_empty.mp haveL]
      · simp [C,active,low]
  obtain ⟨u,us,path⟩ := chosen_return free hq reg hs pv hv ph bank none f choose budget
  rw [show q-1=q-3+1+1 by omega] at path
  obtain ⟨y,part,_,last⟩ := path.unsnoc
  obtain ⟨b,initialWalk,ym,incoming⟩ := part.unsnoc
  have old := walk_sub (cut_sub (C:=C)) initialWalk
  have yu := cut_sub _ _ last
  have by' := cut_sub _ _ incoming
  have billed : u∈L y := by
    apply mem_filter.mpr
    refine ⟨us,yu,?_⟩
    rw [show q-2=q-3+1 by omega]
    exact old.snoc ym by'
  by_cases cheap : (L y).card≤1
  · have off : ¬(K y).Nonempty := fun active => separate y active u us yu
    have hit : u∈C y := by simpa only [C,ite_eq_right off,ite_eq_left cheap] using billed
    exact (of_decide_eq_true (Bool.and_eq_true_iff.mp last).2) hit
  · have reach : y∈K b := mem_filter.mpr ⟨ym,by',(show 2≤(L y).card by omega),u,us,yu,old⟩
    have active : (K b).Nonempty := ⟨y,reach⟩
    have hit : y∈C b := by simpa only [C,ite_eq_left active] using reach
    exact (of_decide_eq_true (Bool.and_eq_true_iff.mp incoming).2) hit


theorem collision {D V q s p h} (free : QFree D V q) (hq : 3≤q) (reg : OutEq s D V)
    (hs : 2≤s) (pv : p∈V) (hv : h∈V) (ph : p≠h) (bank : Eligible V {p,h} q (s-1))
    (none : NoHost q (s-1)) (f : ℕ → ℕ)
    (choose : ∀ u∈jointParents D V p h, f u∈heads D V p h ∧ D u (f u)≠true) :
    let U := V \ {p,h}
    let S := jointParents D V p h
    ∃ y∈U, (outN D U y).card=s ∧ ∃ u∈S,∃ v∈S,u≠v ∧ D y u=true ∧ D y v=true ∧
      Walk D U (f u) y (q-2) ∧ Walk D U (f v) y (q-2) ∧
      D u (f v)≠true ∧ D v (f u)≠true := by
  obtain ⟨b,_,_,many⟩ := fork free hq reg hs pv hv ph bank none f choose
  obtain ⟨y,ym⟩ := card_pos.mp (lt_of_lt_of_le (by decide : 0<2) many)
  obtain ⟨yu,_,two,_⟩ := mem_filter.mp ym
  obtain ⟨u,ul,v,vl,ne⟩ := one_lt_card.mp two
  obtain ⟨us,legU,wu⟩ := mem_filter.mp ul
  obtain ⟨vs,legV,wv⟩ := mem_filter.mp vl
  refine ⟨y,yu,tail_spare free reg pv hv (choose _ us).1 yu wu (by omega),
    u,us,v,vs,ne,legU,legV,wu,wv,?_,?_⟩
  · exact fun a => no_back free (by omega) sdiff_subset (parent_data us).1
      (outN_subset (mem_inter.mp (choose _ vs).1).1) wv a legU
  · exact fun a => no_back free (by omega) sdiff_subset (parent_data vs).1
      (outN_subset (mem_inter.mp (choose _ us).1).1) wu a legV

#print axioms fork
#print axioms collision
end LeanCH.BR.CommonHeadLastCut
