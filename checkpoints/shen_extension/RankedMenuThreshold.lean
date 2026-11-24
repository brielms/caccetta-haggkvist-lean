import checkpoints.shen_extension.RankedUnitWindow

namespace LeanCH.BR.RankedMenuThreshold
open Finset BRq2 BRq3 WeightedSD Closure RankedHeadChoices

/-- At unit weights, the least number of starts that pays is determined by
    the retained order and the cutoff. The same starts work without pruning. -/
@[aesop safe forward (immediate := [window,hq,sub,room,noLoss,upper]) (rule_sets := [CHGraphFamilies])]
theorem criterion {q r : ℕ} {D : CH.Digraph} {V W : Finset ℕ}
    (window : RankedUnitWindow.WindowLaw q r D V) (hq : 2≤q) (sub : W⊆V)
    (room : (V\W).card<1+q*r) (noLoss : 1+q*r≤(V\W).card+q) (upper : V.card≤1+q*r) :
    let U := V\W
    (∃E : CH.Digraph,(∀i j,E i j=true → D i j=true) ∧ ∃H⊆U,H.Nonempty ∧
       mass U (fun _=>1)<(q:ℚ)*mass H (fun _=>1) ∧ RowBills q E U H (fun _=>1) (q-2)) ↔
        U.card/q+1≤(FlatPeelReach.interior D V U (q-1)).card := by
  intro U
  let K := FlatPeelReach.interior D V U (q-1)
  have inspect := window.tests W sub room noLoss upper
  change heads q D U (fun _=>1) (q-2)=K ∧ ∀ E : CH.Digraph,(∀i j,E i j=true → D i j=true) →
    heads q E U (fun _=>1) (q-2) ⊆ K at inspect
  have asCount (S : Finset ℕ) : mass U (fun _=>1)<(q:ℚ)*mass S (fun _=>1) ↔ U.card/q+1≤S.card := by
    simp only [mass,sum_const,nsmul_eq_mul,mul_one]
    have bound : U.card/q<S.card ↔ U.card<q*S.card := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0<q),Nat.mul_comm]
    constructor
    · intro bill
      have whole : U.card<q*S.card := by exact_mod_cast bill
      exact bound.mpr whole
    · intro enough
      exact_mod_cast bound.mp enough
  constructor
  · rintro ⟨E,edges,H,hs,_,heavy,paid⟩
    exact ((asCount H).mp heavy).trans (card_le_card (((row_bills_iff (by omega) hs).mp paid).trans
      (inspect.2 E edges)))
  · intro enough
    refine ⟨D,fun _ _ hit=>hit,?_⟩
    apply (exists_menu_iff (q:=q) (by omega) (fun _ _=>(by decide : (0:ℚ)≤1))).mpr
    rw [inspect.1]
    exact (asCount K).mpr enough

#print axioms criterion
end LeanCH.BR.RankedMenuThreshold
