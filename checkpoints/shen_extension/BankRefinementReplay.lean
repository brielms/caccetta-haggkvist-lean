import checkpoints.shen_extension.PairPowerDeletion
import checkpoints.shen_extension.FourLayerSharedSource
import checkpoints.shen_extension.FourTargetChoice
import checkpoints.shen_extension.TwoSinkPayer
import checkpoints.shen_extension.TripleBankMenu

/-! Transport the numerical and labelled repair results to the two native
source alternatives reached by the capstone. The triangle conclusions keep
the cutoff guard and the newly selected bank labels. -/
namespace LeanCH.BR.BankRefinementReplay
open Finset BRq2 BRq3 BR45 CHRuleCatalog BypassRepair BypassBankReplay JointShortcutReplay
open JointFreeTargets
open scoped Classical

@[aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])]
theorem counterexample_degree {c : Input} (bad : Bad c) : 10 ≤ c.s := by
  by_contra! small
  exact bad.missing (LeanCH.Results.degree_one_to_nine c.D bad.order bad.degree_pos (by omega)
    bad.loopless bad.degree)

def DeletionWindow (n s q : ℕ) : Prop :=
  2≤q ∧ n≤q*9+2*(s-9) ∧ (s≤2^(q-1) ∨ n+1<(2^(q/2)+2)*2^(2^(q/2)-1))

@[aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])]
theorem outside_deletion_window {c : Input} (bad : Bad c) :
    ¬DeletionWindow c.n c.s (cutoff c) := by
  rintro ⟨hq,cap,gap⟩
  have hs := counterexample_degree bad
  exact bad.missing (PairPowerDeletion.from_degree_nine c.D bad.order (by omega) hq cap gap
    bad.loopless bad.degree)

structure AtTriangle (q : ℕ) (P : Prop) : Prop where
  on_cutoff : q=3 → P

@[aesop safe forward (immediate := [guard,triangle]) (rule_sets := [CHGraphFamilies])]
theorem at_triangle {q : ℕ} {P : Prop} (guard : AtTriangle q P) (triangle : q=3) : P :=
  guard.on_cutoff triangle

section FourTargets
open FourTargetPayment
open FourTargetPayment.Role

/-- The marked incidence and free-repair premises for this particular pool
and nominated payer. The caller supplies their actual labels. -/
structure FourTargetFrame (D : CH.Digraph) (V : Finset ℕ) (p y : ℕ)
    (v : Role ↪ ℕ) (W : Finset ℕ) : Prop where
  live : ∀ i∉targets, v i∈V
  pool : W⊆V
  hit : ∀ i∈shortRows, D (v i) p=true ∧ D (v i) y=true
  heads : ∀ h∈W, D p h=true ∧ D y h=true
  back : ∀ h∈W, ∀ i∈middles, D h (v i)=true
  legs : ∀ i∈middles, ∀ k∈shortRows, D (v i) (v k)=true
  orderX : D (v j) (v x)≠true
  neutral : FourLayerReversal.neutral D p y (v payer)
  retained : v payer≠p ∧ v payer≠y
  payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true
  others : ∀ r∈inN D V p ∩ inN D V y, r∉shortRows.map v →
    ∃ l, FreeTarget D V r l ∧ l∉inN D V p ∩ inN D V y
  one : ∀ e∈V, (∀ i∉targets, e≠v i) → FourLayerReversal.neutral D p y e →
    ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s

noncomputable def exceptions (D : CH.Digraph) (V : Finset ℕ) (p y : ℕ)
    (v : Role ↪ ℕ) (W : Finset ℕ) : Finset ℕ :=
  W.filter (fun h => ¬FourTargetChoice.alternativeReturn D V p y v h)

structure FourTargetLaw (D : CH.Digraph) (V : Finset ℕ) (p y : ℕ) : Prop where
  bounds : ∀ v W, FourTargetFrame D V p y v W →
    (exceptions D V p y v W).card≤4 ∧
      ∀ B⊆exceptions D V p y v W, B.card=4 → ∃ i, Walk D B i i 4

private theorem four_target_law {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1≤t)
    (order : V.card=3*t+2) (no : NoHost 3 t) (pv : p∈V) (yv : y∈V) (py : p≠y) :
    FourTargetLaw D V p y := by
  constructor
  intro v W f
  have bound := FourTargetChoice.at_most_four_without_another v free reg ht order no f.live pv yv py
    f.pool f.hit f.heads f.back f.legs f.orderX f.neutral f.retained f.payerRows f.others f.one
  refine ⟨bound,?_⟩
  intro B be size
  exact FourTargetChoice.four_without_another_cycle v free reg ht order no f.live pv yv py
    f.pool f.hit f.heads f.back f.legs f.orderX f.neutral f.retained f.payerRows f.others f.one
    (be.trans (filter_subset _ _)) size (fun h hb => (mem_filter.mp (be hb)).2)

@[aesop safe forward (immediate := [law,frame]) (rule_sets := [CHGraphFamilies])]
theorem four_target_bound {D V p y v W} (law : FourTargetLaw D V p y)
    (frame : FourTargetFrame D V p y v W) : (exceptions D V p y v W).card≤4 :=
  (law.bounds v W frame).1

@[aesop safe forward (immediate := [law,frame,subset,four]) (rule_sets := [CHGraphFamilies])]
theorem four_target_cycle {D V p y v W B} (law : FourTargetLaw D V p y)
    (frame : FourTargetFrame D V p y v W) (subset : B⊆exceptions D V p y v W) (four : B.card=4) :
    ∃ i, Walk D B i i 4 := (law.bounds v W frame).2 B subset four
end FourTargets

section TwoSinks
open TwoSinkPayer
open TwoSinkPayer.Role
/-- The certified residual and its exterior budgets, before choosing a
vertex on a return into the nominated payer. -/
structure TwoSinkFrame (D : CH.Digraph) (U : Finset ℕ) (t : ℕ) (v : Role ↪ ℕ) : Prop where
  free : QFree D U 3
  inside : ∀ i, v i∈U
  internal : ∀ i k, D (v i) (v k)=true → allowed i k=true
  need : ∀ i∈rows, t≤(outN D U (v i)).card+1
  spare : ∀ i∉rows, t+1≤(outN D U (v i)).card
  floor : ∀ e∈U, (∀ i, e≠v i) → t≤(outN D U e).card
  rich : ∀ e∈U, (∀ i, e≠v i) → (LabelledTrianglePatch.chargesOf gains D v e).Nonempty →
    t+1≤(outN D U e).card
  one : ∀ e∈U, (∀ i, e≠v i) → ∀ r∈rows, ∀ s∈rows, D e (v r)=true → D e (v s)=true → r=s
  old : ∀ e∈U, (∀ i, e≠v i) → ∀ r∈rows, (FourLayerReversal.charges D (oldLabels v r) e).card≤1

structure TwoSinkLaw (U : Finset ℕ) (t : ℕ) : Prop where
  returns : ∀ E v, TwoSinkFrame E U t v →
    ∃ e∈U, (∀ i, e≠v i) ∧ E (v z) e=true ∧ E e (v payer)=true

private theorem two_sink_law {U : Finset ℕ} {t : ℕ} (room : U.card≤3*t) (no : NoHost 3 t) :
    TwoSinkLaw U t := by
  constructor
  intro E v f
  by_contra! none
  have clear : ∀ e∈U, (∀ i, e≠v i) → E (v z) e=true → E e (v payer)≠true := by
    intro e eu off ze em
    exact (none e eu off ze) em
  obtain ⟨G,safe,_,degree⟩ := TwoSinkPayer.repair_if_clear v f.free f.inside f.internal f.need
    f.spare f.floor f.rich f.one f.old clear
  exact no G U ⟨_,f.inside a⟩ room safe degree

@[aesop safe forward (immediate := [law,frame]) (rule_sets := [CHGraphFamilies])]
theorem two_sink_return {E U t v} (law : TwoSinkLaw U t) (frame : TwoSinkFrame E U t v) :
    ∃ e∈U, (∀ i, e≠v i) ∧ E (v z) e=true ∧ E e (v payer)=true := law.returns E v frame
end TwoSinks

section SharedSource
open FourLayerReversal FourLayerReversal.Role FourLayerSharedSource

/-- The actual eight labels and bank incidences for the shared-source edit. -/
structure SharedSourceFrame (D : CH.Digraph) (V : Finset ℕ) (p y : ℕ)
    (v : Role ↪ ℕ) : Prop where
  live : ∀ i, v i ∈ V
  exactS : inN D V (v a) ∩ inN D V (v b) = {v x,v j}
  hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true
  heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true
  back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true
  legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true
  orderX : D (v j) (v x) ≠ true
  source : ∀ i ∈ targets, D (v i) (v u) ≠ true
  others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
    ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y
  noSwap : ¬∃ m∈V, (∀ i, m ≠ v i) ∧ neutral D p y m ∧ D m (v c)=true ∧
    (D m (v a)=true ∨ D m (v b)=true)

structure SinglePayerFrame (D : CH.Digraph) (V : Finset ℕ) (p y : ℕ)
    (v : Role ↪ ℕ) (m : ℕ) : Prop where
  sink : ∀ i ∈ targets, D (v w) (v i) ≠ true
  single : ∀ e ∈ V, (∀ i, e ≠ v i) → neutral D p y e →
    (2 ≤ (charges D v e).card ∨ 2 ≤ (FourLayerSharedSource.chargesOf gainsS D v e).card) → e = m

structure SharedSourceLaw (D : CH.Digraph) (V : Finset ℕ) (p y : ℕ) : Prop where
  returns : ∀ v, SharedSourceFrame D V p y v →
    ∃ m ∈ V, (∀ i, m ≠ v i) ∧ neutral D p y m ∧
      D (v u) m=true ∧ D m (v j)=true ∧ (D (v w) m=true ∨ D (v z) m=true) ∧
      ∃ i ∈ shortRows, D m (v i)=true
  sole : ∀ v m, SharedSourceFrame D V p y v → SinglePayerFrame D V p y v m →
    D (v w) m=true ∧ D m (v x)=true ∧ D (v u) m=true ∧ D m (v j)=true ∧
      ∃ i ∈ shortRows, D m (v i)=true

private theorem shared_source_law {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1≤t)
    (order : V.card=3*t+2) (no : NoHost 3 t) (pv : p∈V) (yv : y∈V) (py : p≠y) :
    SharedSourceLaw D V p y := by
  constructor
  · intro v f
    exact shared_source_returns v free reg ht order no f.live pv yv py f.exactS f.hit f.heads
      f.back f.legs f.orderX f.source f.others f.noSwap
  · intro v m f g
    exact single_payer_forced v free reg ht order no f.live pv yv py f.exactS f.hit f.heads
      f.back f.legs f.orderX g.sink f.source f.others f.noSwap g.single

@[aesop safe forward (immediate := [law,frame]) (rule_sets := [CHGraphFamilies])]
theorem shared_source_return {D V p y v} (law : SharedSourceLaw D V p y)
    (frame : SharedSourceFrame D V p y v) :
    ∃ m ∈ V, (∀ i, m ≠ v i) ∧ neutral D p y m ∧
      D (v u) m=true ∧ D m (v j)=true ∧ (D (v w) m=true ∨ D (v z) m=true) ∧
      ∃ i ∈ shortRows, D m (v i)=true := law.returns v frame

@[aesop safe forward (immediate := [law,frame,single]) (rule_sets := [CHGraphFamilies])]
theorem sole_payer_heads {D V p y v m} (law : SharedSourceLaw D V p y)
    (frame : SharedSourceFrame D V p y v) (single : SinglePayerFrame D V p y v m) :
    D (v w) m=true ∧ D m (v x)=true ∧ D (v u) m=true ∧ D m (v j)=true ∧
      ∃ i ∈ shortRows, D m (v i)=true := law.sole v m frame single

@[aesop safe forward (immediate := [law,frame,single]) (rule_sets := [CHGraphFamilies])]
theorem sole_payer_hits_middle {D V p y v m} (law : SharedSourceLaw D V p y)
    (frame : SharedSourceFrame D V p y v) (single : SinglePayerFrame D V p y v m) :
    D m (v j)=true := (law.sole v m frame single).2.2.2.1
end SharedSource

/-- A second choice of marked pair on the original carrier, with its
synchronized row counts, targets and applicable payment laws. -/
def SharedTriangleBank {q s : ℕ} (X : ShenMinimumOrder.Source q s) : Prop :=
  ∃ p∈X.V, ∃ y∈X.V, p≠y ∧
    let U := X.V \ {p,y}
    let S := U.filter (fun c => (outN X.D U c).card<s-1)
    3≤S.card ∧ 2≤(lockedRows X.D X.V S).card ∧
    (∃ T⊆outN X.D X.V p ∩ outN X.D X.V y, 2≤T.card ∧
      ∀ z∈T, ∃ x∈S, Marked X ⟨{p,y},x,p,z⟩ ∧ JointShort X ⟨{p,y},x,p,z⟩) ∧
    FourTargetLaw X.D X.V p y ∧ TwoSinkLaw U (s-1) ∧ SharedSourceLaw X.D X.V p y

@[aesop safe forward (immediate := [certificate,common,reg,hs,none]) (rule_sets := [CHGraphFamilies])]
theorem shared_triangle {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (certificate : SelectedParentOrder X m) (common : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hs : 8≤s) (none : NoHost q (s-1)) :
    AtTriangle q (SharedTriangleBank X) := by
  constructor
  rintro rfl
  cases s with
  | zero => omega
  | succ t =>
    have ord := certificate.shared.mp common
    change X.V.card=3*t+2 at ord
    obtain ⟨p,pv,y,yv,py,large,locked,T,sub,count,marks⟩ :=
      RotatedLockedRows.three_short_marked_choices X reg (by omega) ord none
    have both : ({p,y} : Finset ℕ) ⊆ X.V := insert_subset pv (singleton_subset_iff.mpr yv)
    have room : (X.V \ {p,y}).card≤3*t := by rw [card_sdiff_of_subset both,card_pair py,ord]; omega
    exact ⟨p,pv,y,yv,py,large,locked,⟨T,sub,count,marks⟩,
      four_target_law X.free reg (by omega) ord none pv yv py,two_sink_law room none,
      shared_source_law X.free reg (by omega) ord none pv yv py⟩

/-- On the native top-order carrier retain one triple, its common targets,
and the exact outcome of the single-row repair test. -/
def MissedTriangleBank {q s : ℕ} (X : ShenMinimumOrder.Source q s) : Prop :=
  ∃ P⊆X.V, 2≤P.card ∧ ∃ B⊆X.V, B.card=3 ∧ (∀ b∈B, P⊆outN X.D X.V b) ∧
    let U := X.V \ B
    let S := U.filter (fun c => 2≤(outN X.D B c).card)
    (∀ c∈S, ∃ z∈P, X.D c z≠true) ∧
    (∀ c∈S, ∃ E : CH.Digraph, QFree E U 3 ∧
      (outN E U c).card=(outN X.D U c).card+(TripleBank.rowMenu X.D U P c).card ∧
      ∀ a∈U, a≠c → min (s-1) (outN E U a).card=min (s-1) (outN X.D U a).card) ∧
    (2≤S.card ∨ ∃ c, S={c} ∧ (outN X.D B c).card=3 ∧ (TripleBank.rowMenu X.D U P c).card=1)

@[aesop safe forward (immediate := [certificate,miss,reg,hs,none,order,cap]) (rule_sets := [CHGraphFamilies])]
theorem missed_triangle {q s n} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (certificate : SelectedParentOrder X m) (miss : MissedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hs : 8≤s) (none : NoHost q (s-1)) (order : X.V.card≤n) (cap : n≤q*s) :
    AtTriangle q (MissedTriangleBank X) := by
  constructor
  rintro rfl
  have lower := certificate.missed.mp miss
  have lim := order.trans cap
  have ord : X.V.card=3*s := by omega
  exact TripleBank.top_repair_frontier X.free reg (by omega) ord none

ch_family_split_predicate SharedTriangleBank
ch_family_split_predicate MissedTriangleBank

#print axioms counterexample_degree
#print axioms outside_deletion_window
#print axioms shared_triangle
#print axioms missed_triangle
#print axioms four_target_bound
#print axioms four_target_cycle
#print axioms two_sink_return
#print axioms shared_source_return
#print axioms sole_payer_heads
#print axioms sole_payer_hits_middle
end LeanCH.BR.BankRefinementReplay
