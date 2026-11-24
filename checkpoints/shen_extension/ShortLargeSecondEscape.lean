import checkpoints.shen_extension.TwoLayerParentCapacity
import checkpoints.shen_extension.ShortFirstFrontier

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock OneOmissionSinkBank
open scoped Classical

/-- When a physical cycle leaves one spare head in the first layer and the
second layer has size r, the third layer cannot have two fewer labels.
The acyclic and cyclic alternatives use the same row budgets. -/
theorem short_large_second_escape {D V q r C u} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (len : q<C.card)
    (rooted : ∀v∈C,Rooted D V v C) (first : C⊆outN D V u)
    (size : C.card+1=r) (ys : (N2 D V u).card=r) (thin : (N3 D V u).card+2≤r) : False := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xsize : X.card=r := reg u uv
  have ysize : Y.card=r := ys
  have zsize : Z.card+2≤r := thin
  have slots : (X\C).card≤1 := by rw [card_sdiff_of_subset first,xsize]; omega
  have cv : C⊆V := first.trans outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have missing c (cm : c∈C) : (Y\outN D V c).card≤2 := by
    have keep : outN D X c⊆outN D C c∪(X\C) := by
      intro a am
      by_cases ac : a∈C
      · exact mem_union_left _ (mem_outN.mpr ⟨ac,(mem_outN.mp am).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨outN_subset am,ac⟩)
    have small := (card_le_card keep).trans (card_union_le _ _)
    rw [(rooted c cm).one c cm] at small
    have reserve := SinkDepthCover.omitted_heads (reg c (cv cm)).ge
      (fun a (am : a∈outN D V c)=>headX (free.mono_bound (by omega : 4≤q)) uv (first cm)
        (outN_subset am) (mem_outN.mp am).2) (by omega : (outN D X c).card≤2)
    change (Y\outN D V c).card+r≤Y.card+2 at reserve
    omega
  by_cases dag : QFree D Y Y.card
  ·
    have ret s (sm : s∈sinks D Y) : ∃x∈C,D s x=true := by
      by_contra! none
      have menu : outN D V s⊆(X\C)∪Z := by
        intro a am
        have edge := (mem_outN.mp am).2
        rcases headY (free.mono_bound (by omega : 4≤q)) uv (mem_filter.mp sm).1 (outN_subset am) edge with early|late
        · have ax := (mem_union.mp early).resolve_right (fun ay=>(mem_filter.mp sm).2 a ay edge)
          exact mem_union_left _ (mem_sdiff.mpr ⟨ax,fun ac=>by have := none a ac; simp_all⟩)
        · exact mem_union_right _ late
      have bound := (card_le_card menu).trans (card_union_le _ _)
      rw [reg s (yv (mem_filter.mp sm).1)] at bound
      omega
    have limit := returning_sink_budget free yv cv dag (by omega : 2+2≤q)
      (fun x xm=>((rooted x xm).one x xm).ge) missing ret
    have lower := Nat.mul_le_mul_left Y.card (show 5≤q-1 by omega)
    omega
  obtain ⟨K,ky,kl,kr⟩ := actual_cycle free (by omega) yv dag
  have kg := card_le_card ky
  have gap := card_sdiff_of_subset ky
  have yroom : (Y\K).card≤1 := by omega
  have cap := two_layer_columns free (by omega) (outN_subset : X⊆V) yv first ky kr kl
    (fun w wm=>(reg w ((mem_union.mp wm).elim (fun m=>outN_subset m) (fun m=>yv m))).ge)
    (fun w wm a am=>headX (free.mono_bound (by omega : 4≤q)) uv wm (outN_subset am) (mem_outN.mp am).2)
    (fun w wm a am=>mem_union.mpr (headY (free.mono_bound (by omega : 4≤q)) uv wm (outN_subset am) (mem_outN.mp am).2))
    missing (by omega) slots yroom ysize.le (by omega : Z.card+1<r)
  change K.card≤(X\C).card*2+(Y\K).card*max 2 (K.card-(q-1)) at cap
  have spare := Nat.mul_le_mul_right (max 2 (K.card-(q-1))) yroom
  rw [Nat.one_mul] at spare
  omega

/-- A surviving one-omission payer has exclusively cyclic primary claims,
and all primary representatives reach at least three times the degree.
All claims are still attached to the same cycle after the transfers. -/
theorem remaining_medium_primary {D V q r target δ cap C A} (free : QFree D V q)
    (reg : OutEq r D V) (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t)
    (ready : RoutingRoom q r V.card target) (mark : RemainingPayer t C δ cap A)
    (width : (exterior D V C).card=r) (size : C.card+1=r) (enough : 2*(r-q+1)<C.card)
    (margin : 4*6<3*C.card+6) :
    (∀Y∈claims t C,¬QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card) ∧
    ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card := by
  classical
  have never : ¬∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ (ball D V (t.rep Y) 3).card<3*r := by
    intro someShort
    obtain ⟨Y,ym,first,sh,yw,zw⟩ := short_first_frontier free reg t policy ready mark width size margin someShort
    have ⟨key,id⟩ := mem_filter.mp ym
    have roots := t.rooted _ (t.assigned _ key)
    have length := t.length _ (t.assigned _ key)
    rw [id] at roots length
    have hr := ready.growth.2.1
    exact short_large_second_escape free ready.cycle.1 reg (rep_native t key) ready.close length roots first size
      ((congrArg card (rep_key t key)).trans yw) (by omega)
  refine ⟨(remaining_orientation mark width size enough).resolve_right never,?_⟩
  intro Y ym first
  exact le_of_not_gt (fun h=>never ⟨Y,ym,first,h⟩)

#print axioms remaining_medium_primary
#print axioms short_large_second_escape
end LeanCH.BR.LowShellCycleSelection
