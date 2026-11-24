import Mathlib.Combinatorics.Enumerative.DoubleCounting
import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BR45KillC

/-!
Physical bank routing on finite digraphs. Distinct claims routed to a shared
terminal are counted at one marked bank, with a per-parent multiplicity bound.
The order-48 example keeps its local graph suppliers as explicit hypotheses.
-/

namespace LeanCH.BR.ExclusiveBankRouting
open Finset BRq2 BRq3 BR45

/-- Two disjoint physical pools cannot both fit in a smaller receiving row. -/
theorem pool_conflict {α : Type*} [DecidableEq α] {A B P : Finset α} (sep : Disjoint A B)
    (left : A⊆P) (right : B⊆P) : A.card+B.card≤P.card := by
  rw [←card_union_of_disjoint sep]
  exact card_le_card (union_subset left right)

/-- In a relation with unique incoming edges, two finite paths ending at the
same vertex have the same origin if neither origin has an incoming edge. -/
theorem same_origin {ι : Type*} {step : ι→ι→Prop}
    (unique : ∀{a b c},step a c → step b c → a=b) {a b z}
    (first : ∀i,¬step i a) (second : ∀i,¬step i b)
    (pa : Relation.ReflTransGen step a z) (pb : Relation.ReflTransGen step b z) : a=b := by
  induction pa with
  | refl =>
    cases pb with
    | refl => rfl
    | tail _ edge => exact (first _ edge).elim
  | tail prev edge ih =>
    cases pb with
    | refl => exact (second _ edge).elim
    | tail prev' edge' => exact ih (unique edge' edge ▸ prev')

/-- All claims reaching the marked terminal must be funded by the parent pool
of a single start. The multiplicity is charged at actual physical parents. -/
theorem terminal_claim_budget {ι κ : Type*} [DecidableEq κ] {C : Finset κ} {z : ι}
    (step : ι→ι→Prop) (bank : ι→Finset ℕ) (mark : ι→ℕ) (origin : κ→ι)
    (parents : κ→Finset ℕ) (D : CH.Digraph) (V : Finset ℕ) {b k δ t : ℕ}
    (size : ∀i,b≤(bank i).card) (apart : ∀i j,i≠j → Disjoint (bank i) (bank j))
    (sends : ∀i j,step i j → bank i⊆inN D V (mark j))
    (indeg : ∀j,(inN D V (mark j)).card≤δ) (two : δ<b+b)
    (claimSize : ∀e∈C,k≤(parents e).card)
    (incoming : ∀e∈C,parents e⊆inN D V (mark (origin e)))
    (separate : ∀e∈C,∀i,step i (origin e) → Disjoint (parents e) (bank i))
    (noRoom : δ<k+b)
    (arrive : ∀e∈C,Relation.ReflTransGen step (origin e) z)
    (reuse : ∀v,(C.filter (fun e=>v∈parents e)).card≤t) :
    C.card*k≤δ*t := by
  classical
  have unique {i j a} (ia : step i a) (ja : step j a) : i=j := by
    by_contra diff
    have cap := (pool_conflict (apart i j diff) (sends i a ia) (sends j a ja)).trans (indeg a)
    have := size i
    have := size j
    omega
  have start e (em : e∈C) (i) (edge : step i (origin e)) : False := by
    have cap := (pool_conflict (separate e em i edge) (incoming e em) (sends i _ edge)).trans (indeg _)
    have := claimSize e em
    have := size i
    omega
  rcases C.eq_empty_or_nonempty with empty|⟨e,em⟩
  · simp [empty]
  let P := inN D V (mark (origin e))
  have within j (jm : j∈C) : parents j⊆P := by
    have eq := same_origin (step:=step) (a:=origin j) (b:=origin e) (z:=z) (fun e₁ e₂=>unique e₁ e₂) (start j jm) (start e em) (arrive j jm) (arrive e em)
    simpa only [P,eq] using incoming j jm
  have covered j (jm : j∈C) : parents j ⊆ P.bipartiteAbove (fun a v=>v∈parents a) j :=
    fun v vm=>mem_filter.mpr ⟨within j jm vm,vm⟩
  have count : C.card*k≤P.card*t := card_mul_le_card_mul (fun a v=>v∈parents a)
    (fun j jm=>(claimSize j jm).trans (card_le_card (covered j jm))) (fun v _=>reuse v)
  exact count.trans (Nat.mul_le_mul_right _ (indeg _))

theorem order48_receipt_limit {m : ℕ} (bound : m*5≤11*2) : m≤4 := by omega
#print axioms same_origin
#print axioms pool_conflict
#print axioms terminal_claim_budget
#print axioms order48_receipt_limit
end LeanCH.BR.ExclusiveBankRouting

namespace LeanCH.BR.ExclusiveBankRouting

inductive Trace {ι : Type*} (step : ι→ι→Prop) (root : ι) : ℕ→ι→Prop
  | start : Trace step root 0 root
  | next {k u v} : Trace step root k u → step u v → Trace step root (k+1) v

theorem trace_rigid {ι : Type*} {step : ι→ι→Prop}
    (unique : ∀{a b c},step a c → step b c → a=b) {a b z k l}
    (first : ∀i,¬step i a) (second : ∀i,¬step i b)
    (left : Trace step a k z) (right : Trace step b l z) : a=b ∧ k=l := by
  induction left generalizing l with
  | start =>
    cases right with
    | start => exact ⟨rfl,rfl⟩
    | next _ edge => exact (first _ edge).elim
  | next prev edge ih =>
    cases right with
    | start => exact (second _ edge).elim
    | next prev' edge' =>
      obtain ⟨ab,len⟩ := ih (unique edge' edge ▸ prev')
      exact ⟨ab,congrArg (·+1) len⟩

theorem Trace.append {ι : Type*} {step : ι→ι→Prop} {a b z k l}
    (left : Trace step a k b) (right : Trace step b l z) : Trace step a (k+l) z := by
  induction right with
  | start => exact left
  | next _ edge ih => exact Trace.next ih edge

/-- Along an exclusive chain starting where no predecessor fits, even a
return to the identical bank at a later positive depth is impossible. -/
theorem no_revisit {ι : Type*} {step : ι→ι→Prop}
    (unique : ∀{a b c},step a c → step b c → a=b) {a z k l}
    (first : ∀i,¬step i a) (entered : Trace step a k z) (loop : Trace step z (l+1) z) : False := by
  have same := (trace_rigid (step:=step) (a:=a) (b:=a) (z:=z) unique first first entered (entered.append loop)).2
  omega

#print axioms trace_rigid
#print axioms no_revisit
end LeanCH.BR.ExclusiveBankRouting

namespace LeanCH.BR.ExclusiveBankRouting
open Finset BRq2 BRq3 BR45

/-- The indegree allowance used by the routing count from the original labels
and cutoff. Balls include the marked vertex. -/
theorem parent_room {q D V a} (hq : 0<q) (safe : QFree D V q) (av : a∈V) :
    (inN D V a).card ≤ V.card-(ball D V a (q-1)).card := by
  classical
  have off : inN D V a⊆V\ball D V a (q-1) := by
    intro i parent
    refine mem_sdiff.mpr ⟨(mem_inN.mp parent).1,?_⟩
    intro reached
    obtain ⟨_,k,bound,path⟩ := mem_ball.mp reached
    exact safe a (k+1) (by omega) (by omega) (path.snoc av (mem_inN.mp parent).2)
  have sub : ball D V a (q-1)⊆V := fun i hi=>(mem_ball.mp hi).1
  simpa only [card_sdiff_of_subset sub] using card_le_card off

/-- Number of literal claims at one terminal using the inclusive (q-1)-balls
of its eligible marked predecessors. -/
theorem terminal_ball_budget {ι κ : Type*} [DecidableEq κ] {C : Finset κ} {z : ι}
    (step : ι→ι→Prop) (bank : ι→Finset ℕ) (mark : ι→ℕ) (origin : κ→ι)
    (parents : κ→Finset ℕ) (D : CH.Digraph) (V : Finset ℕ) {q b k m t : ℕ}
    (hq : 0<q) (free : QFree D V q) (inside : ∀i,mark i∈V)
    (layers : ∀i,m≤(ball D V (mark i) (q-1)).card)
    (size : ∀i,b≤(bank i).card) (apart : ∀i j,i≠j → Disjoint (bank i) (bank j))
    (sends : ∀i j,step i j → bank i⊆inN D V (mark j))
    (two : V.card-m<b+b)
    (claimSize : ∀e∈C,k≤(parents e).card)
    (incoming : ∀e∈C,parents e⊆inN D V (mark (origin e)))
    (separate : ∀e∈C,∀i,step i (origin e) → Disjoint (parents e) (bank i))
    (noRoom : V.card-m<k+b)
    (arrive : ∀e∈C,Relation.ReflTransGen step (origin e) z)
    (reuse : ∀v,(C.filter (fun e=>v∈parents e)).card≤t) :
    C.card*k≤(V.card-m)*t :=
  terminal_claim_budget step bank mark origin parents D V size apart sends
    (fun j=>(parent_room hq free (inside j)).trans (Nat.sub_le_sub_left (layers j) V.card))
    two claimSize incoming separate noRoom arrive reuse

/-- The order-48 application uses the physical first-hop incidence bounds
from the atlas. Every hypothesis here still has to be supplied in Lean at 48. -/
theorem four_at_48 {ι κ : Type*} [DecidableEq κ] {C : Finset κ} {z : ι}
    (step : ι→ι→Prop) (bank : ι→Finset ℕ) (mark : ι→ℕ) (origin : κ→ι)
    (parents : κ→Finset ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (order : V.card=48) (free : QFree D V 6) (inside : ∀i,mark i∈V)
    (layers : ∀i,37≤(ball D V (mark i) 5).card)
    (size : ∀i,7≤(bank i).card) (apart : ∀i j,i≠j → Disjoint (bank i) (bank j))
    (sends : ∀i j,step i j → bank i⊆inN D V (mark j))
    (claimSize : ∀e∈C,5≤(parents e).card)
    (incoming : ∀e∈C,parents e⊆inN D V (mark (origin e)))
    (separate : ∀e∈C,∀i,step i (origin e) → Disjoint (parents e) (bank i))
    (arrive : ∀e∈C,Relation.ReflTransGen step (origin e) z)
    (reuse : ∀v,(C.filter (fun e=>v∈parents e)).card≤2) :
    C.card≤4 := by
  have budget := terminal_ball_budget (q:=6) (b:=7) (k:=5) (m:=37) (t:=2)
    step bank mark origin parents D V (by decide) free inside layers size apart sends
    (by omega) claimSize incoming separate (by omega) arrive reuse
  rw [order] at budget
  exact order48_receipt_limit budget

#print axioms four_at_48
#print axioms parent_room
#print axioms terminal_ball_budget
end LeanCH.BR.ExclusiveBankRouting
