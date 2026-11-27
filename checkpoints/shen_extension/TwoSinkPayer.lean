import checkpoints.shen_extension.FourLayerReversal
import checkpoints.shen_extension.LabelledTrianglePatch

/-! Explicit two-sink edit. The previously nominated payer also reverses
onto a sink. Exterior vertices can now be billed for a leg into that payer. -/
namespace LeanCH.BR.TwoSinkPayer
open Finset BRq2 BRq3 BR45
open LabelledTrianglePatch (chargesOf)
inductive Role | a | b | c | x | j | u | w | z | payer
  deriving DecidableEq
open Role
instance : Fintype Role := ⟨{a,b,c,x,j,u,w,z,payer},fun i => by cases i <;> simp⟩
local instance (p : Role → Prop) [DecidablePred p] : Decidable (∀ i, p i) :=
  Fintype.decidableForallFintype

def rows : Finset Role := {a,b,c}
def mids : Finset Role := {x,j}
def heads : Finset Role := {u,w,z}

def gains : Role → Finset Role
  | .a | .x => {w} | .b | .c => {u} | .payer => {z} | _ => ∅
def cuts : Role → Finset Role
  | .j => {a} | .payer => {a,x} | .u => {j} | .w => {x}
  | .x => {b,c} | .z => {payer} | _ => ∅

def allowed (i k : Role) : Bool := decide (i≠k ∧
  ¬(i∈rows ∧ k∈mids) ∧ ¬(i∈mids ∧ k∈heads) ∧
  ¬(i∈rows ∧ k∈heads) ∧ ¬(i∈heads ∧ k∈rows) ∧
  ¬(i=j ∧ k=x) ∧ ¬((i=w ∨ i=z) ∧ k∈heads) ∧
  ¬(i=payer ∧ (k=b ∨ k=c ∨ k=z)) ∧ ¬(i∈mids ∧ k=payer))

private theorem shape :
    (∀ i, ∀ h ∈ gains i, h ≠ i ∧ allowed i h = false ∧
      (allowed h i = false ∨ i ∈ cuts h) ∧ gains h = ∅) ∧
    (∀ i, ∀ h ∈ gains i, ∀ m, allowed h m=true → allowed m i=true →
      m∈cuts h ∨ i∈cuts m) ∧
    (∀ i, if i∈rows then (cuts i).card+1≤(gains i).card
      else (cuts i).card≤1+(gains i).card) := by decide

theorem repair {D : CH.Digraph} {U : Finset ℕ} {t : ℕ} (v : Role ↪ ℕ)
    (free : QFree D U 3) (inside : ∀ i, v i∈U)
    (internal : ∀ i k, D (v i) (v k)=true → allowed i k=true)
    (need : ∀ i∈rows, t≤(outN D U (v i)).card+1)
    (spare : ∀ i∉rows, t+1≤(outN D U (v i)).card)
    (pay : ∀ e∈U, (∀ i, e≠v i) → t+(chargesOf gains D v e).card ≤ (outN D U e).card) :
    ∃ G : CH.Digraph, QFree G U 3 ∧ (∀ i, ∀ h∈gains i, G (v i) (v h)=true) ∧
      ∀ e∈U, t≤(outN G U e).card :=
  LabelledTrianglePatch.repair_of_shape v rows gains cuts allowed shape.1 shape.2.1 shape.2.2
    free inside internal need spare pay

private abbrev Old := FourLayerReversal.Role

/-- Reorder the rows so that r receives its intended target in a reversal
with sink w. The remaining row assignments do not affect its bill. -/
def layout (r : Role) : Old → Role
  | .a => if r=c then c else b
  | .b => a
  | .c => if r=c then b else c
  | .x => x | .j => j | .u => u | .w => w | .z => z

def oldLabels (v : Role ↪ ℕ) (r : Role) : Old ↪ ℕ where
  toFun i := v (layout r i)
  inj' := fun i k eq =>
    (show ∀ r, ∀ i k, layout r i=layout r k → i=k by decide) r _ _ (v.injective eq)

/-- If this exterior vertex has at most one short-row leg and does not
defeat the old reversals, its double bill includes z→e→payer. -/
theorem new_return {D : CH.Digraph} {v : Role ↪ ℕ} {e : ℕ}
    (two : 2≤(chargesOf gains D v e).card)
    (one : ∀ r∈rows, ∀ s∈rows, D e (v r)=true → D e (v s)=true → r=s)
    (old : ∀ r∈rows, (FourLayerReversal.charges D (oldLabels v r) e).card≤1) :
    D (v z) e=true ∧ D e (v payer)=true := by
  classical
  let C := chargesOf gains D v e
  have leg {i} (hi : i∈C) := (mem_filter.mp hi).2.1
  have via {i} (hi : i∈C) := (mem_filter.mp hi).2.2
  have payerDue : payer∈C := by
    by_contra notDue
    have part {i} (ci : i∈C) : i=x ∨ i∈rows := by
      obtain ⟨h,hg,_⟩ := via ci
      rcases (show ∀ i, ∀ h∈gains i, i=payer ∨ i=x ∨ i∈rows by decide) i h hg with rfl | rem
      · exact False.elim (notDue ci)
      · exact rem
    obtain ⟨i,ic,k,kc,ne⟩ := one_lt_card.mp two
    obtain ⟨r,hr,rc,xc⟩ : ∃ r∈rows, r∈C ∧ x∈C := by
      rcases part ic with rfl | ir <;> rcases part kc with rfl | kr
      · exact False.elim (ne rfl)
      · exact ⟨k,kr,kc,ic⟩
      · exact ⟨i,ir,ic,kc⟩
      · exact False.elim (ne (one _ ir _ kr (leg ic) (leg kc)))
    obtain ⟨h,hg,he⟩ := via rc
    obtain ⟨l,lg,le⟩ := via xc
    have lw : l=w := by simpa [gains] using lg
    let slot : Old := if r=a then .b else .a
    have eq : layout r slot=r := (show ∀ r∈rows, layout r (if r=a then .b else .a)=r by decide) r hr
    have pick := (show ∀ r∈rows, ∀ h∈gains r, ∃ k∈FourLayerReversal.gains (if r=a then .b else .a),
      layout r k=h by decide) r hr h hg
    obtain ⟨k,bg,be⟩ := pick
    have bill : 2≤(FourLayerReversal.charges D (oldLabels v r) e).card := by
      refine one_lt_card.mpr ⟨slot,?_,.x,?_,by dsimp [slot]; split <;> decide⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _,?_,k,bg,?_⟩
        · change D e (v (layout r slot))=true
          rw [eq]; exact leg rc
        · change D (v (layout r k)) e=true
          rwa [be]
      · exact mem_filter.mpr ⟨mem_univ _,leg xc,.w,by decide,by change D (v w) e=true; rwa [←lw]⟩
    have small := old r hr
    omega
  obtain ⟨h,hg,he⟩ := via payerDue
  have hz : h=z := by simpa [gains] using hg
  exact ⟨hz ▸ he,leg payerDue⟩

/-- A two-sink host on the actual residual when the remaining return
into the designated payer is absent. -/
theorem repair_if_clear {D : CH.Digraph} {U : Finset ℕ} {t : ℕ} (v : Role ↪ ℕ)
    (free : QFree D U 3) (inside : ∀ i, v i∈U)
    (internal : ∀ i k, D (v i) (v k)=true → allowed i k=true)
    (need : ∀ i∈rows, t≤(outN D U (v i)).card+1)
    (spare : ∀ i∉rows, t+1≤(outN D U (v i)).card)
    (floor : ∀ e∈U, (∀ i, e≠v i) → t≤(outN D U e).card)
    (rich : ∀ e∈U, (∀ i, e≠v i) → (chargesOf gains D v e).Nonempty → t+1≤(outN D U e).card)
    (one : ∀ e∈U, (∀ i, e≠v i) → ∀ r∈rows, ∀ s∈rows, D e (v r)=true → D e (v s)=true → r=s)
    (old : ∀ e∈U, (∀ i, e≠v i) → ∀ r∈rows, (FourLayerReversal.charges D (oldLabels v r) e).card≤1)
    (clear : ∀ e∈U, (∀ i, e≠v i) → D (v z) e=true → D e (v payer)≠true) :
    ∃ G : CH.Digraph, QFree G U 3 ∧ (∀ i, ∀ h∈gains i, G (v i) (v h)=true) ∧
      ∀ e∈U, t≤(outN G U e).card := by
  classical
  apply repair v free inside internal need spare
  intro e eu off
  have cost : (chargesOf gains D v e).card≤1 := by
    by_contra! fail
    obtain ⟨ze,em⟩ := new_return fail (one e eu off) (old e eu off)
    exact clear e eu off ze em
  by_cases pos : (chargesOf gains D v e).Nonempty
  · have := rich e eu off pos
    omega
  · rw [not_nonempty_iff_eq_empty.mp pos,card_empty,Nat.add_zero]
    exact floor e eu off

#print axioms repair_if_clear
#print axioms repair
#print axioms new_return
end LeanCH.BR.TwoSinkPayer
