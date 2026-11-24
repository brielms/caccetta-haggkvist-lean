import checkpoints.shen_extension.MinimumOrbitEscape

namespace LeanCH.BR.Closure.TriangleReachableRoles
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights PuncturedSquareRoles

def Edge (D : CH.Digraph) (W M N : Finset ℕ) : Prop :=
  Cycle D W 3 N ∧ PunctureCycleLoop.Step D M N

abbrev Reach (D : CH.Digraph) (W seed : Finset ℕ) :=
  Relation.ReflTransGen (Edge D W) seed

def Seen (D : CH.Digraph) (W seed : Finset ℕ) (t : ℕ) : Prop :=
  ∃M,Reach D W seed M ∧ t∈M

/-- A marked label comes with a particular incoming move and its two
parents in the previous state. A general visit need not give that witness. -/
def Marked (D : CH.Digraph) (W seed : Finset ℕ) (r : ℕ) : Prop :=
  Cycle D W 3 seed ∧ ∃M N,Reach D W seed M ∧ Cycle D W 3 N ∧ r∈N\M ∧ 2≤(inN D M r).card

theorem missed_roles {n} (X : Model 3 n) {h seed r t}
    (marked : Marked X.D (X.V\{h}) seed r) (tw : t∈X.V\{h})
    (absent : ¬Seen X.D (X.V\{h}) seed t) :
    role X.D h r≠role X.D h t ∧
    (role X.D h r=.head → role X.D h t=.opposite → X.D r t=true) ∧
    (role X.D h r=.opposite → role X.D h t=.parent → X.D r t=true) := by
  obtain ⟨_,M,N,path,c,rn,rich⟩ := marked
  have rw' := c.sub (mem_sdiff.mp rn).1
  have edge : Edge X.D (X.V\{h}) M N := ⟨c,r,rn,rich⟩
  have rt : r≠t := fun eq => absent ⟨N,path.tail edge,eq ▸ (mem_sdiff.mp rn).1⟩
  apply forced X (mem_sdiff.mp rw').1 (mem_sdiff.mp tw).1
    (by simpa using (mem_sdiff.mp rw').2) (by simpa using (mem_sdiff.mp tw).2) rt
  rintro ⟨K,ck,rk,tk⟩
  exact absent ⟨K,path.tail (show Edge X.D (X.V\{h}) M K from
    ⟨ck,r,mem_sdiff.mpr ⟨rk,(mem_sdiff.mp rn).2⟩,rich⟩),tk⟩

/-- A marked receiver covers its entire root-role class. The source for the
next move is the very same reachable state that supplied that mark. -/
theorem covers_role {n} (X : Model 3 n) {h seed r t}
    (marked : Marked X.D (X.V\{h}) seed r) (tw : t∈X.V\{h})
    (same : role X.D h r=role X.D h t) : Seen X.D (X.V\{h}) seed t := by
  by_contra absent
  exact (missed_roles X marked tw absent).1 same

/-- A sufficient coverage condition on any reachable family of four-cycles. -/
theorem covers_puncture {n} (X : Model 3 n) {h seed}
    (marks : ∀i : Role,∃r,Marked X.D (X.V\{h}) seed r ∧ role X.D h r=i) :
    ∀t∈X.V\{h},Seen X.D (X.V\{h}) seed t := by
  intro t tw
  obtain ⟨r,m,eq⟩ := marks (role X.D h t)
  exact covers_role X m tw eq

/-- Marks propagate to a retained common head whenever its two different
parents have the same root role and one parent was already marked. -/
theorem propagate {n} (X : Model 3 n) {h seed r s t} (hv : h∈X.V)
    (minimum : ∀x∈X.V,X.weights h≤X.weights x) (large : 13≤X.V.card)
    (marked : Marked X.D (X.V\{h}) seed r) (sw : s∈X.V\{h}) (tw : t∈X.V\{h})
    (distinct : r≠s) (rt : X.D r t=true) (st : X.D s t=true)
    (equal : role X.D h r=role X.D h s) : Marked X.D (X.V\{h}) seed t := by
  classical
  obtain ⟨seedCycle,M,N,path,c,rn,rich⟩ := marked
  have rw' := c.sub (mem_sdiff.mp rn).1
  obtain ⟨K,ck,rk,sk⟩ : ∃K,Cycle X.D (X.V\{h}) 3 K ∧ r∈K ∧ s∈K := by
    by_contra miss
    exact (forced X (mem_sdiff.mp rw').1 (mem_sdiff.mp sw).1
      (by simpa using (mem_sdiff.mp rw').2) (by simpa using (mem_sdiff.mp sw).2) distinct miss).1 equal
  have step : Edge X.D (X.V\{h}) M K := ⟨ck,r,mem_sdiff.mpr ⟨rk,(mem_sdiff.mp rn).2⟩,rich⟩
  have two : 2≤(inN X.D K t).card := one_lt_card.mpr
    ⟨r,mem_inN.mpr ⟨rk,rt⟩,s,mem_inN.mpr ⟨sk,st⟩,distinct⟩
  have out : t∉K := fun tk => by
    have one : (inN X.D K t).card=1 := ck.incoming t tk
    omega
  obtain ⟨L,cl,tl⟩ := PunctureCycleLoop.cover X large hv minimum tw
  exact ⟨seedCycle,K,L,path.tail step,cl,mem_sdiff.mpr ⟨tl,out⟩,two⟩

/-- A directed rule on original labels with the second parent retained as
a witness. Paths in this relation preserve the property of being marked. -/
def Next (D : CH.Digraph) (W : Finset ℕ) (h r t : ℕ) : Prop :=
  t∈W ∧ D r t=true ∧ ∃s∈W,r≠s ∧ D s t=true ∧ role D h r=role D h s

theorem propagate_path {n} (X : Model 3 n) {h seed r t} (hv : h∈X.V)
    (minimum : ∀x∈X.V,X.weights h≤X.weights x) (large : 13≤X.V.card)
    (marked : Marked X.D (X.V\{h}) seed r)
    (route : Relation.ReflTransGen (Next X.D (X.V\{h}) h) r t) :
    Marked X.D (X.V\{h}) seed t := by
  induction route with
  | refl => exact marked
  | tail _ step ih =>
    obtain ⟨tw,rt,s,sw,distinct,st,e⟩ := step
    exact propagate X hv minimum large ih sw tw distinct rt st e

theorem propagation_for_capstone {q n} (X : Model q n) : q=3 →
    ∀h∈X.V,(∀x∈X.V,X.weights h≤X.weights x) → 13≤X.V.card → ∀seed r t,
      Marked X.D (X.V\{h}) seed r → Relation.ReflTransGen (Next X.D (X.V\{h}) h) r t →
      Marked X.D (X.V\{h}) seed t := by
  rintro rfl h hv m l seed r t marked path
  exact propagate_path X hv m l marked path

#print axioms propagate_path

theorem coverage_for_capstone {q n} (X : Model q n) : q=3 →
    ∀h seed t,t∈X.V\{h} → (∃r,Marked X.D (X.V\{h}) seed r ∧ role X.D h r=role X.D h t) →
      Seen X.D (X.V\{h}) seed t := by
  rintro rfl h seed t tw ⟨r,m,eq⟩
  exact covers_role X m tw eq

#print axioms covers_puncture
#print axioms coverage_for_capstone
end LeanCH.BR.Closure.TriangleReachableRoles
