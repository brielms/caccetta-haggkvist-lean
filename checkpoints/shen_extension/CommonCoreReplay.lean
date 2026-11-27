import checkpoints.shen_extension.CommonCoreGrowth
import checkpoints.shen_extension.CommonHeadCutReplay

namespace LeanCH.BR.CommonCoreReplay
open Finset BRq2 BRq3 BypassRepair BypassBankReplay JointShortcutReplay
open CommonCoreCompression CommonHeadCutReplay

/-- For each specific head removed from this row, retain the actual
family of rows which still cover all its other heads. -/
structure RowCoreBound (D : CH.Digraph) (V : Finset ℕ) (s p : ℕ) : Prop where
  bound : ∀ z∈outN D V p, (parents D V ((outN D V p).erase z)).card+3 ≤ s

theorem row_bound {D V q s p} (free : QFree D V q) (hq : 3≤q) (hs : 3≤s)
    (reg : OutEq s D V) (order : V.card=q*(s-1)+2) (lower : ∀ k,k<s → NoHost q k)
    (pv : p∈V) : RowCoreBound D V s p := by
  refine ⟨?_⟩
  intro z zm
  let B := (outN D V p).erase z
  let T := parents D V B
  have sz : B.card=s-1 := by simp [B,card_erase_of_mem zm,reg p pv]
  have bv : B⊆V := (erase_subset ..).trans outN_subset
  have tv : T⊆V := filter_subset _ _
  change T.card+3≤s
  by_contra! many
  have eq : s-1+1=s := by omega
  exact no_near_rectangle (T:=T) (P:=B) free hq (by omega : 2≤s-1)
    (by simpa only [eq] using reg) order (by simpa only [eq] using lower) tv bv
    (by omega) sz.ge (fun a at' b bp => (mem_outN.mp ((mem_filter.mp at').2 bp)).2)

@[aesop safe forward (immediate := [cert,shared,_law,reg,hq,hs,lower,pv,hv]) (rule_sets := [CHGraphFamilies])]
theorem shared_rows {q s p h} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (cert : SelectedParentOrder X m) (shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_law : ForkLaw X.D X.V q s p h) (reg : OutEq s X.D X.V)
    (hq : 3≤q) (hs : 8≤s) (lower : ∀ k,k<s → NoHost q k)
    (pv : p∈X.V) (hv : h∈X.V) : RowCoreBound X.D X.V s p ∧ RowCoreBound X.D X.V s h :=
  ⟨row_bound X.free hq (by omega) reg (cert.shared.mp shared) lower pv,
   row_bound X.free hq (by omega) reg (cert.shared.mp shared) lower hv⟩

ch_family_split_result shared_rows

#print axioms row_bound
#print axioms shared_rows
end LeanCH.BR.CommonCoreReplay
