import checkpoints.shen_extension.ShortestCyclePeeling

namespace LeanCH.BR.Closure.ShortestCycleDescent
open Finset BRq2 BRq3 BR45 ShortestCyclePeeling ShortestCycleClasses

/-- One node parameterizes actual spanning graphs on the same finite set.
The fields certify the counterexample conditions at the current cutoff. -/
structure Frame (V : Finset ℕ) where
  graph : CH.Digraph
  q : ℕ
  s : ℕ
  cutoff : 2≤q
  safe : QFree graph V q
  order : V.card≤q*s
  degree : ∀x∈V,s≤(outN graph V x).card

/-- Only an actual spanning subgraph with the new cutoff and degree may be
a successor. The property fields of the target frame certify both. -/
def Step {V} (a b : Frame V) : Prop :=
  b.q=a.q+1 ∧ b.s=a.s-a.s/(a.q+1) ∧ ∀x y, b.graph x y=true → a.graph x y=true

theorem cutoff_lt {V} (a : Frame V) (live : V.Nonempty) : a.q<V.card := by
  have positive := card_pos.mpr live
  have sp : a.s≠0 := by
    intro eq
    have le := a.order
    rw [eq,Nat.mul_zero] at le
    omega
  have one (x) (xv : x∈V) : 1≤(outN a.graph V x).card := by have := a.degree x xv; omega
  have hq := a.cutoff
  have le := dt_size (by omega : 1≤a.q) (ball_q_one a.q (by omega)) a.safe one live
  simpa using le

/-- Induction over the actual transitions. Each edge raises q on the same
carrier, so even when the integer degree loss is zero there is no loop. -/
theorem descend {V} (live : V.Nonempty) (a : Frame V) :
    ∃b : Frame V, Reach Step a b ∧ ∃T⊆V,Dense b.graph T b.q (b.s/(b.q+1)) ∧
      ∀x∈T,carrier b.graph T b.q x=T := by
  let k := a.s/(a.q+1)
  have hq := a.cutoff
  rcases peel_or_raise (by omega : 1≤a.q) a.safe a.degree k with found|⟨E,sub,free,deg⟩
  · exact ⟨a,.refl,recurrent_of_dense found⟩
  · have budget : V.card≤(a.q+1)*(a.s-k) := by
      have div := Nat.mod_add_div a.s (a.q+1)
      have ord := a.order
      rw [Nat.mul_sub,Nat.add_mul a.q 1 a.s,Nat.one_mul]
      dsimp only [k]
      omega
    let b : Frame V := ⟨E,a.q+1,a.s-k,by omega,free,budget,deg⟩
    have edge : Step a b := ⟨rfl,rfl,sub⟩
    obtain ⟨c,path,core⟩ := descend live b
    exact ⟨c,(Relation.ReflTransGen.single edge).trans path,core⟩
termination_by V.card-a.q
decreasing_by
  have lt := cutoff_lt a live
  change V.card-(a.q+1)<V.card-a.q
  omega

theorem from_input {D V q s} (hq : 2≤q) (free : QFree D V q) (live : V.Nonempty)
    (order : V.card≤q*s) (degree : ∀x∈V,s≤(outN D V x).card) :
    ∃b : Frame V, Reach Step (⟨D,q,s,hq,free,order,degree⟩ : Frame V) b ∧
      ∃T⊆V,Dense b.graph T b.q (b.s/(b.q+1)) ∧ ∀x∈T,carrier b.graph T b.q x=T :=
  descend live _

/-- These nodes literally are sets of digraphs, indexed by degree and
cutoff on a fixed set of labels. An edge has a witness for each source
graph outside the recurrent-core subclass. -/
def family (V : Finset ℕ) (q s : ℕ) : Set CH.Digraph :=
  {D | 2≤q ∧ QFree D V q ∧ V.card≤q*s ∧ ∀x∈V,s≤(outN D V x).card}

def coreFamily (V : Finset ℕ) (q s : ℕ) : Set CH.Digraph :=
  {D | ∃T⊆V,Dense D T q (s/(q+1)) ∧ ∀x∈T,carrier D T q x=T}

theorem family_edge {D V q s} (src : D∈family V q s \ coreFamily V q s) :
    ∃E∈family V (q+1) (s-s/(q+1)),∀x y,E x y=true → D x y=true := by
  obtain ⟨⟨hq,free,ord,degree⟩,outside⟩ := src
  rcases peel_or_raise (by omega : 1≤q) free degree (s/(q+1)) with core|⟨E,sub,safe,deg⟩
  · exact (outside (recurrent_of_dense core)).elim
  · refine ⟨E,⟨by omega,safe,?_,deg⟩,sub⟩
    have div := Nat.mod_add_div s (q+1)
    rw [Nat.mul_sub,Nat.add_mul q 1 s,Nat.one_mul]
    omega

/-- Discharge only recurrent members of reachable parameter families.
Well-founded propagation then discharges the entire starting family. -/
theorem family_induction {V : Finset ℕ} (live : V.Nonempty) (allowed : ℕ→ℕ→Prop)
    (next : ∀q s,allowed q s → allowed (q+1) (s-s/(q+1)))
    (terminal : ∀q s,allowed q s → Disjoint (family V q s) (coreFamily V q s))
    {q s} (start : allowed q s) : family V q s=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro D input
  obtain ⟨hq,free,ord,degree⟩ := input
  let a : Frame V := ⟨D,q,s,hq,free,ord,degree⟩
  obtain ⟨b,path,core⟩ := descend live a
  have allowed_b : allowed b.q b.s := by
    clear core
    induction path with
    | refl => exact start
    | tail _ edge ih =>
      obtain ⟨eq,ds,_⟩ := edge
      rw [eq,ds]
      exact next _ _ ih
  exact Set.disjoint_left.mp (terminal _ _ allowed_b)
    (show b.graph∈family V b.q b.s from ⟨b.cutoff,b.safe,b.order,b.degree⟩) core

#print axioms family_edge
#print axioms family_induction
#print axioms descend
#print axioms from_input
end LeanCH.BR.Closure.ShortestCycleDescent
