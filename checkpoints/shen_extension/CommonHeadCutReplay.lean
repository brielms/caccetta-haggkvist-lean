import checkpoints.shen_extension.CommonHeadCutCore
import checkpoints.shen_extension.CommonHeadCutDepth

namespace LeanCH.BR.CommonHeadCutReplay
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay JointShortcutReplay
open CommonHeadLastCut CommonHeadCutDepth

structure Assignment (D : CH.Digraph) (V : Finset ℕ) (p h : ℕ) (f : ℕ → ℕ) : Prop where
  offers : ∀ u∈jointParents D V p h,f u∈heads D V p h ∧ D u (f u)≠true

structure ForkLaw (D : CH.Digraph) (V : Finset ℕ) (q s p h : ℕ) : Prop where
  applies : ∀ f,Assignment D V p h f →
    let U := V \ {p,h}
    ∃ b∈U,(outN D U b).card=s ∧ 2≤(previousBill D U (jointParents D V p h) q f b).card

  fullDepth : ∀ f,Assignment D V p h f →
    let U := V \ {p,h}
    let S := jointParents D V p h
    ∃ u∈S,Branches (routes D U S q f) U S (q-1) (f u)

@[aesop safe forward (immediate := [law,assignment]) (rule_sets := [CHGraphFamilies])]
theorem assigned_tree {D V q s p h f} (law : ForkLaw D V q s p h) (assignment : Assignment D V p h f) :
    let U := V \ {p,h}
    let S := jointParents D V p h
    ∃ u∈S,Branches (routes D U S q f) U S (q-1) (f u) ∧
      2^(q-1) ≤ (words (routes D U S q f) U S (q-1) (f u)).card := by
  obtain ⟨u,us,tree⟩ := law.fullDepth f assignment
  exact ⟨u,us,tree,word_count tree⟩

@[aesop safe forward (immediate := [law,assignment]) (rule_sets := [CHGraphFamilies])]
theorem assigned_fork {D V q s p h f} (law : ForkLaw D V q s p h) (assignment : Assignment D V p h f) :
    ∃ b∈V \ {p,h},(outN D (V \ {p,h}) b).card=s ∧
      2≤(previousBill D (V \ {p,h}) (jointParents D V p h) q f b).card := law.applies f assignment

ch_family_split_result assigned_tree
ch_family_split_result assigned_fork

/-- One selectable pair on the native source. The assignment law and
minimal set of short rows belong to this very same pair. -/
def CommonBank {q s} (X : ShenMinimumOrder.Source q s) : Prop :=
  ∃ p∈X.V,∃ h∈X.V,p≠h ∧
    let P := heads X.D X.V p h
    let S := jointParents X.D X.V p h
    let U := X.V \ {p,h}
    (∀ a∈X.V,∀ b∈X.V,a≠b → (heads X.D X.V a b).card≤P.card) ∧
    (∀ u∈S,∃ z∈P,X.D u z≠true) ∧ ForkLaw X.D X.V q s p h ∧
    (∃ f,Assignment X.D X.V p h f) ∧
    ∃ T⊆S,T.Nonempty ∧ (∀ u∈T,∃ f,Fits X.D U P (T.erase u) q f) ∧
      ∀ u∈T,∀ f,Fits X.D U P (T.erase u) q f → ∀ z∈P,X.D u z≠true →
        ∃ v∈T.erase u,Clash X.D U q u z v (f v) ∧ X.D v z≠true ∧ X.D u (f v)≠true

@[aesop safe forward (immediate := [cert,shared,reg,hs,hq,none]) (rule_sets := [CHGraphFamilies])]
theorem shared_bank {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (cert : SelectedParentOrder X m) (shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hs : 8≤s) (hq : 3≤q) (none : NoHost q (s-1)) :
    CommonBank X := by
  obtain ⟨p,pv,h,hv,ph,best,menu,core⟩ := shared_core cert shared reg (by omega) hq none
  have order := cert.shared.mp shared
  have pos : 0<q*(s-1) := Nat.mul_pos (by omega) (by omega)
  have bs : ({p,h} : Finset ℕ)⊆X.V := insert_subset pv (singleton_subset_iff.mpr hv)
  have two : ({p,h} : Finset ℕ).card=2 := card_pair ph
  have bank : Eligible X.V {p,h} q (s-1) := ⟨bs,by rw [two,order]; omega,
    card_pos.mp (by rw [card_sdiff_of_subset bs,two,order]; omega)⟩
  classical
  let S := jointParents X.D X.V p h
  let pick (u : ℕ) := if us : u∈S then (menu u us).choose else 0
  have assigned : Assignment X.D X.V p h pick := ⟨fun u us => by
    change u∈S at us
    simpa only [pick,dite_eq_left us] using (menu u us).choose_spec⟩
  exact ⟨p,pv,h,hv,ph,best,menu,⟨fun f c => fork X.free hq reg (by omega) pv hv ph bank none f c.offers,
    fun f c => full_depth X.free hq reg (by omega) pv hv ph bank none f c.offers⟩,⟨pick,assigned⟩,core⟩

ch_family_split_predicate CommonBank

#print axioms shared_bank
#print axioms assigned_fork
#print axioms assigned_tree
end LeanCH.BR.CommonHeadCutReplay
