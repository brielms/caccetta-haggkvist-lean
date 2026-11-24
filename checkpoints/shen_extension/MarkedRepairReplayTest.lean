import checkpoints.shen_extension.RootFamilyEntry

namespace LeanCH.BR.MarkedRepairReplayTest
open CHRuleCatalog CHFamilyWorklist CHContextCatalog Lean Meta Elab Tactic

structure Mark (c : Input) (x y : ℕ) : Prop where
  tail : x<c.n
  head : y<c.n
  arc : c.D x y=true

structure Ready (c : Input) (x y : ℕ) : Prop where
  bad : Bad c
  mark : Mark c x y

structure MarkedBad (c : Input) (x y : ℕ) : Prop where
  bad : Bad c
  mark : Mark c x y

structure Carried (c : Input) (x y : ℕ) : Prop where
  evidence : MarkedBad c x y

theorem consume {c x y} (w : MarkedBad c x y) : Carried c x y := ⟨w⟩

@[aesop safe forward (immediate := [bad,mark]) (rule_sets := [CHGraphFamilies])]
theorem ready_at_child {c x y} (bad : Bad c) (mark : Mark c x y) : Ready c x y := ⟨bad,mark⟩

theorem ruleA {c x y} (mark : Mark c x y) (ready : Ready c x y) : MarkedBad c x y :=
  ⟨ready.bad,mark⟩

structure Enabled (p : Input) : Prop where
  bad : Bad p

@[aesop safe forward (immediate := [result]) (rule_sets := [CHGraphFamilies])]
theorem enable {p x y} (result : MarkedBad p x y) : Enabled p := ⟨result.bad⟩

structure Offer (p l r : Input) (a b u v : ℕ) : Prop where
  whenEnabled : Enabled p → (Child p l ∧ Mark l a b) ∨ (Child p r ∧ Mark r u v)

theorem ruleB {p l r a b u v} (offer : Offer p l r a b u v) (go : Enabled p) :
    (Child p l ∧ Mark l a b) ∨ (Child p r ∧ Mark r u v) := offer.whenEnabled go
ch_family_split_result ruleB

structure TypedOffer (p l r : Input) (a b u v : ℕ) : Prop where
  give : Offer p l r a b u v

@[aesop safe forward (immediate := [offer,go]) (rule_sets := [CHGraphFamilies])]
theorem typedB {p l r a b u v} (offer : TypedOffer p l r a b u v) (go : Enabled p) :
    (Child p l ∧ Mark l a b) ∨ (Child p r ∧ Mark r u v) := ruleB offer.give go

elab "check_marked_count " n:num : tactic => withMainContext do
  let mut count := 0
  for d in ← getLCtx do
    if (← instantiateMVars d.type).consumeMData.isAppOf ``MarkedBad then count := count+1
  unless count==n.getNat do throwError "expected {n.getNat} marked applications, found {count}"

elab "check_goal_count " n:num : tactic => do
  let count := (← getGoals).length
  unless count==n.getNat do throwError "expected {n.getNat} open cases, found {count}"

macro "finish_marked" : tactic => `(tactic|
  (replay_ch_families
   check_goal_count 2
   all_goals check_marked_count 2
   all_goals replay_ch_families
   check_goal_count 2
   all_goals check_marked_count 2
   all_goals first | exact Or.inl ⟨by assumption,by assumption⟩
                   | exact Or.inr ⟨by assumption,by assumption⟩))

theorem split_on_entry {n r q} {D : CH.Digraph} (_cut : q=CH.ceilDiv n r)
    {l t : Input} {x y a b u v : ℕ} (_bad : Bad ⟨n,r,D⟩)
    (_m : Mark ⟨n,r,D⟩ x y) (_ready : Ready ⟨n,r,D⟩ x y)
    (_fork : (Child ⟨n,r,D⟩ l ∧ Mark l a b) ∨ (Child ⟨n,r,D⟩ t ∧ Mark t u v)) :
    (Child ⟨n,r,D⟩ l ∧ MarkedBad l a b) ∨ (Child ⟨n,r,D⟩ t ∧ MarkedBad t u v) := by
  with_ch_root_catalog
    ch_on_fact hit of Mark => have produced := ruleA hit (by assumption)
    check_marked_count 1
    finish_marked

theorem split_from_legacy {n r q} {D : CH.Digraph} (_cut : q=CH.ceilDiv n r)
    {l t : Input} {x y a b u v : ℕ} (_bad : Bad ⟨n,r,D⟩)
    (_m : Mark ⟨n,r,D⟩ x y) (_ready : Ready ⟨n,r,D⟩ x y)
    (_offer : Offer ⟨n,r,D⟩ l t a b u v) :
    (Child ⟨n,r,D⟩ l ∧ MarkedBad l a b) ∨ (Child ⟨n,r,D⟩ t ∧ MarkedBad t u v) := by
  with_ch_root_catalog
    ch_on_fact hit of Mark => have produced := ruleA hit (by assumption)
    ch_on_fact choice of Offer => have alternatives := ruleB choice (by assumption)
    check_marked_count 1
    finish_marked

theorem split_from_typed {n r q} {D : CH.Digraph} (_cut : q=CH.ceilDiv n r)
    {l t : Input} {x y a b u v : ℕ} (_bad : Bad ⟨n,r,D⟩)
    (_m : Mark ⟨n,r,D⟩ x y) (_ready : Ready ⟨n,r,D⟩ x y)
    (_offer : TypedOffer ⟨n,r,D⟩ l t a b u v) :
    (Child ⟨n,r,D⟩ l ∧ MarkedBad l a b) ∨ (Child ⟨n,r,D⟩ t ∧ MarkedBad t u v) := by
  with_ch_root_catalog
    ch_on_fact hit of Mark => have produced := ruleA hit (by assumption)
    check_marked_count 1
    finish_marked

/-- A downstream legacy recipe reads the role originally called `produced`.
Both the parent and the child own such a role in each surviving branch. -/
theorem retained_output_roles {n r q} {D : CH.Digraph} (_cut : q=CH.ceilDiv n r)
    {l t : Input} {x y a b u v : ℕ} (_bad : Bad ⟨n,r,D⟩)
    (_m : Mark ⟨n,r,D⟩ x y) (_ready : Ready ⟨n,r,D⟩ x y)
    (_fork : (Child ⟨n,r,D⟩ l ∧ Mark l a b) ∨ (Child ⟨n,r,D⟩ t ∧ Mark t u v)) :
    Carried ⟨n,r,D⟩ x y ∧ ((Child ⟨n,r,D⟩ l ∧ Carried l a b) ∨ (Child ⟨n,r,D⟩ t ∧ Carried t u v)) := by
  with_ch_root_catalog
    ch_on_fact hit of Mark => have produced := ruleA hit (by assumption)
    have consumed := consume produced
    replay_ch_families
    check_goal_count 2
    all_goals check_marked_count 2
    all_goals constructor
    all_goals first | assumption | exact Or.inl ⟨by assumption,by assumption⟩
                    | exact Or.inr ⟨by assumption,by assumption⟩

example (P Q : Prop) (h : P ∨ Q) : P ∨ Q := by
  replay_ch_typed_families
  check_goal_count 1
  exact h

/-- An initially blocked rule stays eligible on another arc of the very
same graph. Neither a new carrier nor a family split is needed. -/
theorem second_arc_on_same_graph {n r q} {D : CH.Digraph} (_cut : q=CH.ceilDiv n r)
    {x y u v : ℕ} (_bad : Bad ⟨n,r,D⟩)
    (_first : Mark ⟨n,r,D⟩ x y) (_second : Mark ⟨n,r,D⟩ u v)
    (_ready : Ready ⟨n,r,D⟩ x y) :
    MarkedBad ⟨n,r,D⟩ x y ∧ MarkedBad ⟨n,r,D⟩ u v := by
  with_ch_root_catalog
    ch_on_fact hit of Mark => have produced := ruleA hit (by assumption)
    check_marked_count 1
    replay_ch_families
    check_goal_count 1
    check_marked_count 2
    replay_ch_families
    check_marked_count 2
    exact ⟨by assumption,by assumption⟩

#print axioms split_on_entry
#print axioms split_from_legacy
#print axioms split_from_typed
#print axioms retained_output_roles
#print axioms second_arc_on_same_graph
end LeanCH.BR.MarkedRepairReplayTest
