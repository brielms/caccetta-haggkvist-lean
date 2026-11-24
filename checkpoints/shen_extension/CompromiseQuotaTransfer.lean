import checkpoints.shen_extension.FlatTurnMatrix
import LeanCH.CompromiseNine
import LeanCH.BR.BRNearBoundaryRows

namespace LeanCH.BR.CompromiseQuotaTransfer
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog ProjectedQuotaTransfer

/-- A local compromise theorem supplies its own degree and score.
The consumer accepts the same lower-quota premise in both orientations. -/
def LowerTest {V : Type} (N : V→Finset V) [DecidableEq V] (d : ℕ) : Prop :=
  ∀S : Finset V,∀k,S.Nonempty → 1≤k → k<d →
    (∀v∈S,k≤(N v∩S).card) → 3*k<S.card

def Supplier (d b : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (A : V→V→Prop) [DecidableRel A],
    (∀v,¬A v v) → (∀u v,A u v → ¬A v u) → (∀u v w,A u v → A v w → ¬A w u) →
    LowerTest (CH.CompromiseSeven.outN A) d → LowerTest (CH.CompromiseSeven.inN A) d →
    (∀v,(CH.CompromiseSeven.outN A v).card=d) →
    (∃v,(CH.CompromiseSeven.outN A v).card≤(CH.CompromiseSeven.second A v).card) →
    ∃v,b≤(CH.CompromiseSeven.second A v).card+(CH.CompromiseSeven.inN A v).card

structure Certificate where
  degree : ℕ
  score : ℕ
  rule : Supplier degree score

def of_supplier {d b} (rule : Supplier d b) : Certificate := ⟨d,b,rule⟩

/-- Import the certified indices from the statement of the existing theorem. -/
-- The only supplier is the degree-nine theorem. `Supplier d b` itself is stated for any d and b.
def recorded := of_supplier (@CH.CompromiseNine.compromise_nine_from_induction)

abbrev adjacency (D : CH.Digraph) (U : Finset ℕ) (x y : ↥U) : Prop := D x.val y.val=true

private theorem measured {D : CH.Digraph} {U : Finset ℕ} (S : Finset ↥U) (v : ↥U) :
    ((CH.CompromiseSeven.outN (adjacency D U) v)∩S).card=(outN D (S.image Subtype.val) v).card := by
  classical
  have sets : ((CH.CompromiseSeven.outN (adjacency D U) v)∩S).image Subtype.val=
      outN D (S.image Subtype.val) v := by
    ext w
    constructor
    · intro h
      obtain ⟨a,am,rfl⟩ := mem_image.mp h
      exact mem_outN.mpr ⟨mem_image_of_mem _ (mem_inter.mp am).2,(by simpa using (mem_inter.mp am).1 : adjacency D U v a)⟩
    · intro h
      obtain ⟨inside,edge⟩ := mem_outN.mp h
      obtain ⟨a,am,rfl⟩ := mem_image.mp inside
      exact mem_image.mpr ⟨a,mem_inter.mpr ⟨(by simpa using (show adjacency D U v a from edge)),am⟩,rfl⟩
  rw [←sets,card_image_of_injective _ Subtype.val_injective]

theorem test_subsets {D U q d} (free : QFree D U q) (cut : 3≤q)
    (lower : ∀k,0<k → k<d → NoHost q k) : LowerTest (CH.CompromiseSeven.outN (adjacency D U)) d := by
  classical
  intro S k live pos small paid
  by_contra! size
  have room : (S.image Subtype.val).card≤q*k := by
    rw [card_image_of_injective _ Subtype.val_injective]
    exact size.trans (Nat.mul_le_mul_right k cut)
  apply lower k pos small D (S.image Subtype.val) (live.image _) room (free.mono_set ?_)
  · intro w wm
    obtain ⟨v,vm,rfl⟩ := mem_image.mp wm
    exact (measured (D:=D) S v) ▸ paid v vm
  · intro w wm
    obtain ⟨v,_,rfl⟩ := mem_image.mp wm
    exact v.property

private theorem order_from_score {V : Type} [Fintype V] [DecidableEq V] {A : V→V→Prop} [DecidableRel A]
    {v d b} (lo : ∀u,¬A u u) (di : ∀u v,A u v → ¬A v u)
    (tri : ∀u v w,A u v → A v w → ¬A w u) (deg : (CH.CompromiseSeven.outN A v).card=d)
    (score : b≤(CH.CompromiseSeven.second A v).card+(CH.CompromiseSeven.inN A v).card) :
    d+b<Fintype.card V := by
  classical
  have pair : Disjoint (CH.CompromiseSeven.outN A v) (CH.CompromiseSeven.inN A v) :=
      disjoint_left.mpr fun a am ai=>di v a (by simpa using am) (by simpa using ai)
  have os : Disjoint (CH.CompromiseSeven.outN A v) (CH.CompromiseSeven.second A v) :=
    disjoint_left.mpr fun a am s=>((CH.CompromiseSeven.mem_second A v a).mp s).2.1 (by simpa using am)
  have ins : Disjoint (CH.CompromiseSeven.inN A v) (CH.CompromiseSeven.second A v) := by
    apply disjoint_left.mpr
    intro a am s
    obtain ⟨_,_,w,vw,wa⟩ := (CH.CompromiseSeven.mem_second A v a).mp s
    exact tri v w a vw wa (by simpa using am)
  have nv : v∉CH.CompromiseSeven.outN A v∪CH.CompromiseSeven.inN A v∪CH.CompromiseSeven.second A v := by simp [lo]
  have card := card_le_card (subset_univ (insert v (CH.CompromiseSeven.outN A v∪CH.CompromiseSeven.inN A v∪CH.CompromiseSeven.second A v)))
  rw [card_insert_of_notMem nv,card_union_of_disjoint (disjoint_union_left.mpr ⟨os,ins⟩),
    card_union_of_disjoint pair,deg,card_univ] at card
  omega

/-- On an exact-degree carrier the compromise witness is a physical row
with its own native parents and two-step destinations. -/
theorem on_exact {q d b E U} (rule : Supplier d b) (cut : 3≤q)
    (lower : ∀k,0<k → k<d → NoHost q k) (safe : QFree E U q)
    (live : U.Nonempty) (reg : OutEq d E U) :
    ∃v∈U,b≤(ShenSeymour.second E U v).card+(inN E U v).card ∧ d+b<U.card := by
  classical
  let A := adjacency E U
  have lo (x : ↥U) : ¬A x x := loopfree safe (by omega) x.property
  have di (x y : ↥U) : A x y → ¬A y x := digonfree safe (by omega) x.property y.property
  have tri (x y z : ↥U) (xy : A x y) (yz : A y z) (zx : A z x) : False :=
    safe x 3 (by decide) cut (.step y.property xy (.step z.property yz (.step x.property zx (.refl _))))
  have imageU : (univ : Finset ↥U).image Subtype.val=U := by ext w; simp
  have row (x : ↥U) : (CH.CompromiseSeven.outN A x).card=d := by
    have eq := measured (D:=E) univ x
    rw [inter_univ,imageU,reg x x.property] at eq
    exact eq
  let : Nonempty ↥U := ⟨⟨live.choose,live.choose_spec⟩⟩
  obtain ⟨y,good⟩ := OAI.SeymourSecondNeighborhood.exists_goodVertex A ⟨lo,fun {x y}=>di x y⟩
  have first : OAI.SeymourSecondNeighborhood.firstNeighbors A y=CH.CompromiseSeven.outN A y := by ext; simp
  have second : OAI.SeymourSecondNeighborhood.secondNeighbors A y=CH.CompromiseSeven.second A y := by ext; simp
  change (OAI.SeymourSecondNeighborhood.firstNeighbors A y).card≤(OAI.SeymourSecondNeighborhood.secondNeighbors A y).card at good
  rw [first,second] at good
  obtain ⟨v,high⟩ := rule A lo di tri (test_subsets safe cut lower)
    (test_subsets safe.reverse cut lower) row ⟨y,good⟩
  have inc := measured (D:=fun a b=>E b a) univ v
  rw [inter_univ,imageU] at inc
  change (CH.CompromiseSeven.inN A v).card=(inN E U v).card at inc
  have images : (CH.CompromiseSeven.second A v).image Subtype.val=ShenSeymour.second E U v := by
    ext w
    constructor
    · intro wm
      obtain ⟨a,am,rfl⟩ := mem_image.mp wm
      obtain ⟨ne,off,z,vz,za⟩ := (CH.CompromiseSeven.mem_second A v a).mp am
      exact mem_filter.mpr ⟨a.property,(fun e=>ne (Subtype.ext e)),off,z.val,z.property,vz,za⟩
    · intro wm
      obtain ⟨wu,ne,off,z,zu,vz,zw⟩ := mem_filter.mp wm
      exact mem_image.mpr ⟨⟨w,wu⟩,(CH.CompromiseSeven.mem_second A v ⟨w,wu⟩).mpr
        ⟨fun e=>ne (congrArg Subtype.val e),off,⟨z,zu⟩,vz,zw⟩,rfl⟩
  refine ⟨v,v.property,?_,by simpa using order_from_score lo di tri (row v) high⟩
  rwa [←images,card_image_of_injective _ Subtype.val_injective,←inc]

theorem apply_supplier {q d b} (rule : Supplier d b) (cut : 3≤q) (positive : 0<d)
    (lower : ∀k,0<k → k<d → NoHost q k) : GuardedFamilyRules.OrderBound q d (d+b) := by
  refine ⟨by omega,?_⟩
  intro D U free live degree
  obtain ⟨E,sub,reg⟩ := exists_outEq degree
  obtain ⟨_,_,_,size⟩ := on_exact rule cut lower (qfree_sub sub free) live reg
  exact size

theorem recorded_bound {p : Input} (bad : Bad p) :
    GuardedFamilyRules.OrderBound (cutoff p) recorded.degree (recorded.degree+recorded.score) := by
  have room : recorded.degree≤projectionFloor := by decide
  have cut := (remaining_from_run p bad).1
  exact apply_supplier recorded.rule cut (by decide) fun k _ hk=>available_lower_hosts bad k (hk.trans_le room)

attribute [aesop safe forward (immediate := [rule,cut,lower,safe,live,reg]) (rule_sets := [CHGraphFamilies])] on_exact
attribute [aesop safe forward (immediate := [rule,cut,positive,lower]) (rule_sets := [CHGraphFamilies])] apply_supplier
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] recorded_bound

#print axioms recorded
#print axioms test_subsets
#print axioms on_exact
#print axioms apply_supplier
#print axioms recorded_bound
end LeanCH.BR.CompromiseQuotaTransfer
