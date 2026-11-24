import checkpoints.shen_extension.ShortFirstStock

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- A short primary class with one spare first head is reconstructed from
the cycle alone: remove from its exterior precisely the labels that point
back to the cycle. Two such classes on one account therefore coincide. -/
theorem recover_first_key {D V q r C u} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (hr : 4≤r) (fit : r≤q+2) (first : C⊆outN D V u)
    (size : C.card+1=r) (width : (exterior D V C).card=r)
    (two : (N2 D V u).card=r-1) :
    N2 D V u=exterior D V C\mutualExterior D V C := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let E := exterior D V C
  have xsize : X.card=r := reg _ uv
  have slots : (X\C).card=1 := by rw [card_sdiff_of_subset first,xsize]; omega
  have balance := gate_balance free hq uv first
  change _+(Y\E).card+E.card=(X\C).card+Y.card at balance
  have ewidth : E.card=r := width
  have ywidth : Y.card=r-1 := two
  have sub : Y⊆E := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega))
  have reach := BankReachTransfer.reaches_bank (k:=1) free (by omega) (outN_subset : X⊆V)
    (fun _ (ym : _∈Y)=>N2_subV ym) disjXY (fun v vm=>by rw [reg v vm]; omega)
    (fun v vm=>by rw [←outN_X_eq (free.mono_bound hq) uv vm,reg v (outN_subset vm)]; dsimp [Y]; omega)
    (by rw [reg u uv]; omega) (by omega) (by rw [reg u uv]; omega)
  have noBack z (zm : z∈Y) : z∉mutualExterior D V C := by
    intro both
    obtain ⟨a,ac⟩ := (mem_filter.mp both).2
    obtain ⟨i,pos,lim,path⟩ := reach a (first (outN_subset ac)) z zm
    exact free a _ (by omega) (by omega) (path.snoc (outN_subset (first (outN_subset ac))) (mem_outN.mp ac).2)
  apply Subset.antisymm (fun z zm=>mem_sdiff.mpr ⟨sub zm,noBack z zm⟩)
  intro z zm
  obtain ⟨ze,notBack⟩ := mem_sdiff.mp zm
  by_contra zy
  have zx := (mem_union.mp (exterior_subset_menu free hq uv first ze)).resolve_right zy
  have all : outN D V z⊆Y := by
    intro w wm
    have reach := headX (free.mono_bound hq) uv (mem_sdiff.mp zx).1 (outN_subset wm) (mem_outN.mp wm).2
    rcases mem_union.mp reach with wx|wy
    · by_cases wc : w∈C
      · exact (notBack (mem_filter.mpr ⟨ze,⟨w,mem_outN.mpr ⟨wc,(mem_outN.mp wm).2⟩⟩⟩)).elim
      have same := card_le_one.mp slots.le w (mem_sdiff.mpr ⟨wx,wc⟩) z zx
      exact (loopfree free (by omega) (outN_subset (mem_sdiff.mp zx).1) (same ▸ (mem_outN.mp wm).2)).elim
    · exact wy
  have := card_le_card all
  rw [reg _ (outN_subset (mem_sdiff.mp zx).1)] at this
  omega

/-- A short row has either consecutive degree-minus-one layers, or the
larger second layer and two fewer slots in the third. -/
theorem short_shapes {D V q r u target} (free : QFree D V q) (reg : OutEq r D V)
    (ready : RoutingRoom q r V.card target) (uv : u∈V) (short : (ball D V u 3).card<3*r) :
    ((N2 D V u).card=r-1 ∧ (N3 D V u).card=r-1) ∨
    ((N2 D V u).card=r ∧ (N3 D V u).card=r-2) := by
  obtain ⟨hq,a,b,c,d,_⟩ := ready.cycle
  have hr := ready.growth.2.1
  have floor := ShellBankOrders.mixed_third free ready.growth reg uv
  have sec := GuardedLayerGrowth.second_floor free (by omega) reg (by omega) (by omega) uv
  have upper := low_third_second free hq reg uv a b c d short.le
  change (ball D V u 2).card≤2*r+1 at upper
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at b1
  have := @card_B2 D V u
  have := @card_B3 D V u
  omega

#print axioms recover_first_key
#print axioms short_shapes
end LeanCH.BR.LowShellCycleSelection
