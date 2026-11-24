import checkpoints.shen_extension.NativeBankDescent

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen ShenSeymour

/-- The good vertex of the erased carrier retains actual intermediaries.
Every old second-layer label it fails to recover is charged to its
own erased out-heads. The opposite alternative names the native row
whose mixed score is strictly below capacity. -/
theorem erased_witness {D U A q} (free : QFree D U q) (cut : 3≤q)
    (sub : A⊆U) (live : (U\A).Nonempty) :
    (∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) ∨
    ∃y∈U\A,
      (outN D (U\A) y).card≤(second D (U\A) y).card ∧
      3*(outN D U y).card+1+
        ((ball D U y 2\ball D U y 1)\second D (U\A) y).card≤U.card+(outN D A y).card := by
  classical
  by_cases hit : ∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card
  · exact Or.inl hit
  right
  have one v (vm : v∈U) := ReachLedger.ball_one free (by omega) vm
  have all := MixedFragmentEscape.score_equality free (by omega : 1+2≤q) (fun _=>U.card+1)
    (fun v vm=>by have low := not_lt.mp (fun h=>hit ⟨v,vm,h⟩); rw [one v vm]; omega)
    (by simp only [sum_const_nat (fun _ _=>rfl),le_refl])
  obtain ⟨y,ym,good⟩ := witness (free.mono_set (sdiff_subset : U\A⊆U)) (by omega : 2≤q) live
  have yu := (mem_sdiff.mp ym).1
  let S := second D (U\A) y
  let Y := ball D U y 2\ball D U y 1
  have inside : S⊆Y := by
    intro z zm
    obtain ⟨zv,ne,miss,t,tm,yt,tz⟩ := mem_filter.mp zm
    refine mem_sdiff.mpr ⟨ball_step (ball_of_adj (mem_sdiff.mp tm).1 yt) (mem_sdiff.mp zv).1 tz,?_⟩
    intro short
    rcases (mem_ball_one yu).mp short with eq|arc
    · exact ne eq
    · exact miss (mem_outN.mp arc).2
  have old := all y yu
  have size : Y.card+(ball D U y 1).card=(ball D U y 2).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 1≤2))
  have lost : (Y\S).card+S.card=Y.card := card_sdiff_add_card_eq_card inside
  have split := card_outN_union (D:=D) (show Disjoint A (U\A) from disjoint_sdiff) y
  rw [union_sdiff_of_subset sub] at split
  rw [one y yu] at old size
  change (outN D (U\A) y).card≤S.card at good
  exact ⟨y,ym,good,by change 3*(outN D U y).card+1+(Y\S).card≤_; omega⟩

/-- With one exception the chosen full row must lose its arc into the
exception, and every missed head of that exception has a replacement
two-step route avoiding the exception. -/
theorem lone_fork {D U q t x} (free : QFree D U q) (cut : 3≤q) (xu : x∈U)
    (other : ∀v∈U,v≠x → t≤(outN D U v).card) (live : (U\{x}).Nonempty)
    (order : U.card≤3*t) :
    (∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) ∨
    ∃y∈U,y≠x ∧ D y x=true ∧ (outN D U y).card=t ∧
      ∀z∈outN D U x,D y z≠true → ∃j∈U,j≠x ∧ D y j=true ∧ D j z=true := by
  classical
  rcases erased_witness free cut (singleton_subset_iff.mpr xu) live with hit|⟨y,ym,_,bill⟩
  · exact Or.inl hit
  right
  obtain ⟨yu,off⟩ := mem_sdiff.mp ym
  have ne : y≠x := by simpa only [mem_singleton] using off
  have paid := other y yu ne
  have cap := card_le_card (outN_subset : outN D {x} y⊆{x})
  rw [card_singleton] at cap
  have one : (outN D {x} y).Nonempty := card_pos.mp (by omega)
  obtain ⟨w,wm⟩ := one
  obtain ⟨wmem,arc⟩ := mem_outN.mp wm
  have hw : w=x := mem_singleton.mp wmem
  subst w
  have clear : ((ball D U y 2\ball D U y 1)\second D (U\{x}) y)=∅ :=
    card_eq_zero.mp (by omega)
  refine ⟨y,yu,ne,arc,by omega,?_⟩
  intro z zm miss
  have zv := outN_subset zm
  have zne : z≠y := by
    intro eq
    subst z
    exact digonfree free (by omega) yu xu arc (mem_outN.mp zm).2
  have inY : z∈ball D U y 2\ball D U y 1 := by
    refine mem_sdiff.mpr ⟨ball_step (ball_of_adj xu arc) zv (mem_outN.mp zm).2,?_⟩
    intro hz
    rcases (mem_ball_one yu).mp hz with eq|adj
    · exact zne eq
    · exact miss (mem_outN.mp adj).2
  have there : z∈second D (U\{x}) y := by
    by_contra no
    have gone := mem_sdiff.mpr ⟨inY,no⟩
    rw [clear] at gone
    exact notMem_empty _ gone
  obtain ⟨_,_,_,j,jm,yj,jz⟩ := mem_filter.mp there
  exact ⟨j,(mem_sdiff.mp jm).1,by simpa only [mem_singleton] using (mem_sdiff.mp jm).2,yj,jz⟩

#print axioms erased_witness
#print axioms lone_fork
end LeanCH.BR.FragmentScoreEquality