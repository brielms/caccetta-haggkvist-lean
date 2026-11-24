import checkpoints.shen_extension.RootFirstArcReturns
import checkpoints.shen_extension.TightCycleSuccessor

namespace LeanCH.BR.Closure.ReturnArcRecurrence
open Finset BRq2 BRq3 BR45 DeficitLevels RootFirstArcReturns

/-- Outgoing arcs whose head reaches an underpaid retained row within q-2 steps. -/
noncomputable def first (D : CH.Digraph) (V : Finset ℕ) (h q s : ℕ) :=
  outN D V h \ ReturnBankOrder.exits D (retained D V h) q s

private theorem head_retained {D V q h a} (free : QFree D V q) (hq : 2≤q) (hv : h∈V)
    (aa : a∈outN D V h) : a∈retained D V h := by
  have ⟨av,ha⟩ := mem_outN.mp aa
  have ah : a≠h := fun e => loopfree free (by omega) hv (e ▸ ha)
  have ai : a∉inN D V h := fun hit => digonfree free hq hv av ha (mem_inN.mp hit).2
  exact mem_sdiff.mpr ⟨av,by simp [ah,ai]⟩

/-- An original induced (q+1)-cycle through both endpoints, with the
designated original arc as the unique successor of h in its support. -/
theorem cycle_of_first {q s} (O : Origin q s) (hq : 2≤q) {h a} (hv : h∈O.V)
    (mem : a∈first O.G O.V h q s) :
    O.G h a=true ∧ ∃M, ShenCycleSuccessor.Cycle O.G O.V q M ∧ h∈M ∧ a∈M := by
  classical
  let W := retained O.G O.V h
  obtain ⟨aa,absent⟩ := mem_sdiff.mp mem
  have aw := head_retained O.free hq hv aa
  have miss : ¬(∀i∈ReturnBankOrder.shortRows O.G W s, ∀k, k+2≤q → ¬Walk O.G W a i k) :=
    fun far => absent (mem_filter.mpr ⟨aw,far⟩)
  push Not at miss
  obtain ⟨z,short,k,le,walk⟩ := miss
  obtain ⟨zw,under⟩ := mem_filter.mp short
  have total := row_count (D:=O.G) zw
  have deg := O.deg z (mem_sdiff.mp zw).1
  change (outN O.G W z).card + (outN O.G (inN O.G O.V h) z).card=_ at total
  change (outN O.G W z).card<s at under
  obtain ⟨b,bz⟩ := card_pos.mp (show 0<(outN O.G (inN O.G O.V h) z).card by omega)
  obtain ⟨bi,zb⟩ := mem_outN.mp bz
  obtain ⟨bv,bh⟩ := mem_inN.mp bi
  have bh' : b≠h := fun e => loopfree O.free (by omega) hv (e ▸ bh)
  have sub : W⊆O.V\{h} := by
    intro x xw
    obtain ⟨xv,n⟩ := mem_sdiff.mp xw
    exact mem_sdiff.mpr ⟨xv,fun eq => n (mem_insert.mpr (Or.inl (mem_singleton.mp eq)))⟩
  have path := (walk.mono sub).snoc (mem_sdiff.mpr ⟨bv,by simpa using bh'⟩) zb
  have close : Walk O.G O.V h h (k+3) := .step (outN_subset aa) (mem_outN.mp aa).2
    ((path.mono sdiff_subset).snoc hv bh)
  have len : k+1=q-1 := by
    have forbid : ¬k+3≤q := fun small => O.free h (k+3) (by omega) small close
    omega
  rw [len] at path
  obtain ⟨M,cycle,_,hm,am⟩ := ShenCycleSuccessor.marked_cycle hq O.free hv (outN_subset aa) bh
    (mem_outN.mp aa).2 path
  exact ⟨(mem_outN.mp aa).2,M,cycle,hm,am⟩

/-- Each original incoming arc contributes one unit to a capacity bound
on the count of outgoing arcs that begin shortest possible cycles. -/
theorem at_root {q s} (O : Origin q s) (hq : 2≤q) {h} (hv : h∈O.V) :
    (inN O.G O.V h).card+q*((outN O.G O.V h).card-s)≤q*(first O.G O.V h q s).card := by
  classical
  let I := inN O.G O.V h
  let A := outN O.G O.V h
  let W := retained O.G O.V h
  let E := ReturnBankOrder.exits O.G W q s
  have wv : W⊆O.V := sdiff_subset
  have iv : I⊆O.V := filter_subset _ _
  have hI : h∉I := fun hi => loopfree O.free (by omega) hv (mem_inN.mp hi).2
  have total : W.card+(I.card+1)=O.V.card := by
    have eq := card_sdiff_add_card_eq_card (insert_subset hv iv)
    rwa [card_insert_of_notMem hI] at eq
  have cap (x) (xw : x∈W) : s≤(outN O.G W x).card+I.card := by
    have eq := row_count (D:=O.G) xw
    change (outN O.G W x).card+(outN O.G I x).card=_ at eq
    have mx := card_le_card (show outN O.G I x⊆I from outN_subset)
    have dg := O.deg x (wv xw)
    omega
  have ib : I.card≤q*(s-E.card) := ReturnBankOrder.same_order O (by omega) wv (by omega) cap
  have min : s≤A.card := O.deg h hv
  have ipos : 0<I.card := by
    by_contra! zero
    have pos := card_pos.mpr O.ne
    have ord := O.order
    have sp : s≠0 := by
      intro eq
      have zeroProduct : q*s=0 := by simp only [eq,Nat.mul_zero]
      omega
    obtain ⟨a,aa⟩ := card_pos.mp (show 0<A.card by omega)
    have least := O.least O.G W (O.free.mono_set wv) (fun x xw => by have := cap x xw; omega)
      ⟨a,head_retained O.free hq hv aa⟩
    omega
  have eh : E.card≤s := by
    by_contra! many
    rw [Nat.sub_eq_zero_of_le many.le,Nat.mul_zero] at ib
    omega
  have split := card_sdiff_add_card_inter A E
  have al := card_le_card (show A∩E⊆E from inter_subset_right)
  have cnt : (s-E.card)+(A.card-s)≤(A\E).card := by omega
  have scaled := Nat.mul_le_mul_left q cnt
  rw [Nat.mul_add] at scaled
  change I.card+q*(A.card-s)≤q*(A\E).card
  omega

/-- At least 1/q of all original arcs start a (q+1)-cycle. Counting
each ordered pair just once avoids any multiplicity of cycle witnesses. -/
theorem arc_share {q s} (O : Origin q s) (hq : 2≤q) :
    (∑h∈O.V,(outN O.G O.V h).card)≤q*(∑h∈O.V,(first O.G O.V h q s).card) := by
  have per (h) (hv : h∈O.V) : (inN O.G O.V h).card≤q*(first O.G O.V h q s).card :=
    (Nat.le_add_right _ _).trans (at_root O hq hv)
  have total := sum_le_sum per
  rw [←mul_sum] at total
  have eq : (∑h∈O.V,(outN O.G O.V h).card)=(∑h∈O.V,(inN O.G O.V h).card) := by
    simp only [inN,outN,card_filter]
    exact sum_comm
  exact eq.trans_le total

theorem recurrent {q s} (O : Origin q s) (hq : 2≤q) (laws : ∀j<s, OrderLaw q j (q*j+1))
    {C : Finset ℕ} (cv : C⊆O.V) (proper : C.card<O.V.card) (live : C.Nonempty)
    (renew : ∀h∈C,first O.G O.V h q s⊆C) :
    ∃h∈C,(inN O.G O.V h).card+q*((outN O.G O.V h).card-s)+1≤C.card := by
  obtain ⟨h,hc,low⟩ := PaidLayerDescent.light O laws cv proper live
  have inc : first O.G O.V h q s⊆outN O.G C h := fun a ha =>
    mem_outN.mpr ⟨renew h hc ha,(mem_outN.mp (mem_sdiff.mp ha).1).2⟩
  have bound := (at_root O hq (cv hc)).trans (Nat.mul_le_mul_left q (card_le_card inc))
  exact ⟨h,hc,by omega⟩

#print axioms cycle_of_first
#print axioms at_root
#print axioms arc_share
#print axioms recurrent
end LeanCH.BR.Closure.ReturnArcRecurrence
