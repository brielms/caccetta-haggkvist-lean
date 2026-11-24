import checkpoints.shen_extension.MiddleReturnBudgets

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock OneOmissionSinkBank
open scoped Classical

/-- When the next shell is exactly the cycle exterior, the exceptional first
row can pay for only a bounded set of sink ancestors. An actual cycle
survives in the second shell, with its labels retained. -/
theorem same_exterior_cycle {D V u C q r} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (uv : u∈V) (first : C⊆outN D V u) (len : q<C.card) (cy : ∀c∈C,Rooted D V c C)
    (fit : r≤q+2) (size : C.card+1=r) (ys : (N2 D V u).card=r)
    (zs : (N3 D V u).card<r) (same : exterior D V C=N2 D V u) :
    ∃K⊆N2 D V u,q<K.card ∧ (N2 D V u\K).card≤1 ∧ ∀x∈K,Rooted D V x K := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have cv := first.trans xv
  obtain ⟨miss,returning⟩ := middle_return_budgets free (by omega) reg uv first len cy size ys same
  have diff := card_sdiff_of_subset first
  rw [reg u uv] at diff
  have gap : (X\C).card=1 := by dsimp [X]; omega
  have ret s (sm : s∈sinks D Y) : ∃x∈X,D s x=true := by
    by_contra! none
    have sub : outN D V s⊆Z := by
      intro a am
      apply (headY (free.mono_bound (by omega : 4≤q)) uv (mem_filter.mp sm).1 (outN_subset am) (mem_outN.mp am).2).resolve_left
      intro hit
      rcases mem_union.mp hit with ax|ay
      · have := none a ax; have := (mem_outN.mp am).2; simp_all
      · exact (mem_filter.mp sm).2 a ay (mem_outN.mp am).2
    have bound := card_le_card sub
    rw [reg _ (yv (mem_filter.mp sm).1)] at bound
    change Z.card<r at zs; omega
  have pos c (cm : c∈C) := ((cy c cm).one c cm).ge
  have nd : ¬QFree D Y Y.card := by
    intro dag
    by_cases hit : ∃w∈X\C,∃y∈Y,D y w=true
    · obtain ⟨w,wm,y,ym,yw⟩ := hit
      have all x (xm : x∈X) : (Y\outN D V x).card≤3 := by
        by_cases xc : x∈C
        · exact (miss x xc).trans (by decide)
        have eq := card_le_one.mp gap.le x (mem_sdiff.mpr ⟨xm,xc⟩) w wm
        subst x
        have := returning w wm ⟨y,ym,yw⟩
        change (Y\outN D V w).card+_≤C.card at this; omega
      obtain ⟨S,_,charge,cover⟩ := separate_sink_budgets free yv xv first dag (by omega : 3+2≤q) pos miss all ret
      rw [gap,mul_one,one_mul] at cover
      rw [Nat.mul_one] at charge
      have small : S.card≤1 := by
        by_contra! many
        have := Nat.mul_le_mul_right (q-1) (show 2≤S.card by omega)
        omega
      change Y.card=r at ys; omega
    · have plain s (sm : s∈sinks D Y) : ∃c∈C,D s c=true := by
        obtain ⟨x,xm,arc⟩ := ret s sm
        exact ⟨x,by by_contra off; exact hit ⟨x,mem_sdiff.mpr ⟨xm,off⟩,s,(mem_filter.mp sm).1,arc⟩,arc⟩
      have bill := returning_sink_budget free yv cv dag (by omega : 1+2≤q) pos miss plain
      simp only [Nat.mul_one] at bill
      have lo := Nat.mul_le_mul_left Y.card (show 1≤q-1 by omega)
      change Y.card=r at ys; omega
  obtain ⟨K,ky,kl,roots⟩ := actual_cycle free (by omega) yv nd
  exact ⟨K,ky,kl,by change (Y\K).card≤1; have := card_sdiff_of_subset ky; change Y.card=r at ys; omega,roots⟩

/-- A second-layer cycle can neither return directly to the extra row nor
send a head to another row that returns there. Both journeys would force
more omitted heads than that same extra row can afford. -/
theorem no_middle_return {D V Y K q w a y l e} (free : QFree D V q) (yv : Y⊆V) (wv : w∈V)
    (ky : K⊆Y) (roots : ∀k∈K,Rooted D V k K) (long : 1<K.card) (ak : a∈K)
    (before : Walk D V a y l) (last : D y w=true) (room : e+(l+1)<q)
    (budget : (Y\outN D V w).card≤e) : False := by
  have miss := missed_cycle_segment free (ky.trans yv) roots long ak wv (before.snoc wv last) (by omega)
  have incl : K\outN D V w⊆Y\outN D V w := fun b bm=>mem_sdiff.mpr ⟨ky (mem_sdiff.mp bm).1,(mem_sdiff.mp bm).2⟩
  have := (card_le_card incl).trans budget
  omega

#print axioms same_exterior_cycle
#print axioms no_middle_return
end LeanCH.BR.LowShellCycleSelection
