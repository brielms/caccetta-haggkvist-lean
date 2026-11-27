import checkpoints.shen_extension.CyclicLayerCount
import checkpoints.shen_extension.CommonHeadCutReplay

namespace LeanCH.BR.CyclicLayerReplay
open Finset BRq2 BRq3 BypassRepair BypassBankReplay JointShortcutReplay
open CommonHeadCutReplay CyclicLayerCount

/-- The named rows come from the cyclic layers of the first bank label. -/
def Representatives (D : CH.Digraph) (V : Finset ℕ) (q p : ℕ) (r : ℕ → ℕ) : Prop :=
  (∀ i < q, r i ∈ ring D V q p (i+1)) ∧ r q = p

/-- Charge the actual rows on the original digraph. -/
def Budget (D : CH.Digraph) (V : Finset ℕ) (q p : ℕ) (r : ℕ → ℕ) : Prop :=
  let L := layer D V q p
  let O := V \ (range (q+1)).biUnion L
  O.card + q*q + q*((range (q+1)).biUnion (fun i => (outN D O (r i)))).card ≤
    1 + q*(∑ i∈range (q+1), (outN D (earlier L q i) (r i)).card) +
      q*(∑ i∈range (q+1), (outN D O (r i)).card)

/-- Keep the two deleted labels, the assignment that supplied the cycle,
and a single row function for both layer conclusions. -/
def CountedBank (D : CH.Digraph) (V : Finset ℕ) (q p h : ℕ)
    (f : ℕ → ℕ) : Prop :=
  Assignment D V p h f ∧ ∃ r, Representatives D V q p r ∧ Budget D V q p r

@[aesop safe forward (immediate := [cert, shared, reg, hs, hq, lower, _law, assignment, pv, hv, ph])
    (rule_sets := [CHGraphFamilies])]
theorem counted_bank {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    {p h : ℕ} {f : ℕ → ℕ}
    (cert : SelectedParentOrder X m) (shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hs : 2 ≤ s) (hq : 3 ≤ q)
    (lower : ∀ t, t < s → NoHost q t)
    (_law : ForkLaw X.D X.V q s p h) (assignment : Assignment X.D X.V p h f)
    (pv : p ∈ X.V) (hv : h ∈ X.V) (ph : p ≠ h) :
    CountedBank X.D X.V q p h f := by
  classical
  have order := cert.shared.mp shared
  have sub : ({p,h} : Finset ℕ) ⊆ X.V := insert_subset pv (singleton_subset_iff.mpr hv)
  have two : ({p,h} : Finset ℕ).card = 2 := card_pair ph
  have pos : 0 < q*(s-1) := Nat.mul_pos (by omega) (by omega)
  have bank : Eligible X.V {p,h} q (s-1) :=
    ⟨sub, by rw [two, order]; omega,
      card_pos.mp (by rw [card_sdiff_of_subset sub, two, order]; omega)⟩
  have degree : s - 1 + 1 = s := by omega
  obtain ⟨r, rows, last, count⟩ := bank_layer_inequality
    X.free hq (by simpa only [degree] using reg) (by omega) pv hv ph bank
    (lower _ (by omega)) (by simpa only [degree] using lower) order f assignment.offers
  exact ⟨assignment, r, ⟨rows, last⟩, count⟩

ch_family_split_predicate CountedBank

#print axioms counted_bank
end LeanCH.BR.CyclicLayerReplay
