import checkpoints.shen_extension.CHForwardCatalog
import checkpoints.shen_extension.RecursivePackingRules
import checkpoints.shen_extension.ParentCutFrontier
import checkpoints.shen_extension.SharedArcComponentExchange
import checkpoints.shen_extension.CHContextCatalog

namespace LeanCH.BR.PackingForwardRules
open Finset BRq2 BRq3 BR45 Closure Closure.FirstPacketBarrier Closure.ShortestCycleWeights
open Closure.SharedArcBarrier

def ColumnBudget {q n} (X : Model q n) (F : MarkedCyclePeeling.Family) (a b : ℕ) : Prop :=
  let E := graph X.D F
  (∑C∈MarkedCyclePeeling.col E F (a,b),
    (1:ℚ)/2^((ExteriorPacking.exterior E X.V C\(outN E X.V a).erase b).card)) ≤ 1

@[aesop safe forward (immediate := [native, boundary]) (rule_sets := [CHGraphFamilies])]
theorem attached_family {q n} {X : Model q n} {F L} (native : F⊆family X)
    (boundary : Boundary X F L) : insert L F⊆family X := insert_subset boundary.1 native

@[aesop safe forward (immediate := [_boundary, edge]) (rule_sets := [CHGraphFamilies])]
theorem retained_edge {q n} {X : Model q n} {F L a b} (_boundary : Boundary X F L)
    (edge : graph X.D F a b=true) : graph X.D (insert L F) a b=true :=
  SharedArcComponentExchange.union_arc.mpr (.inl edge)

@[aesop safe forward (immediate := [native, edge]) (rule_sets := [CHGraphFamilies])]
theorem selected_budget {q n} {X : Model q n} {F a b} (native : F⊆family X)
    (edge : graph X.D F a b=true) : ColumnBudget X F a b := by
  classical
  by_cases pos : 1≤q
  · exact ExteriorPacking.selected_arc_budget X pos F native (a,b)
  obtain ⟨C,cm⟩ := active.mp edge
  obtain ⟨cf,ac,bc,ab⟩ := MarkedCyclePeeling.mem_col.mp cm
  have cy := (mem_filter.mp (native cf)).2
  have one : C.card≤1 := by have := cy.size; omega
  have eq := card_le_one.mp one a ac b bc
  subst b
  -- At cutoff zero every native support is a singleton. The chosen arc
  -- determines that entire support, even when it is a loop.
  let E := graph X.D F
  let A := MarkedCyclePeeling.col E F (a,a)
  have small : A⊆{ {a} } := by
    intro B bm
    obtain ⟨bf,ba,_,_⟩ := MarkedCyclePeeling.mem_col.mp bm
    have cyc := (mem_filter.mp (native bf)).2
    have size : B.card=1 := by have := cyc.size; omega
    exact mem_singleton.mpr (eq_of_subset_of_card_le (singleton_subset_iff.mpr ba)
      (by simp [size])).symm
  change (∑C∈A,(1:ℚ)/2^_) ≤ 1
  calc
    _ ≤ ∑_C∈A,(1:ℚ) := sum_le_sum (fun _ _=>by
      apply (div_le_one (by positivity)).mpr
      exact one_le_pow₀ (by norm_num))
    _ = (A.card:ℚ) := by simp
    _ ≤ 1 := by exact_mod_cast (show A.card≤1 by simpa using card_le_card small)

attribute [aesop safe forward (immediate := [b,e]) (rule_sets := [CHGraphFamilies])]
  CHRuleCatalog.bad_child
attribute [aesop safe forward (immediate := [b,path]) (rule_sets := [CHGraphFamilies])]
  CHRuleCatalog.bad_descendant

@[aesop safe forward (immediate := [deg,missing,loop,hn,hr]) (rule_sets := [CHGraphFamilies])]
theorem bad_input {n r D} (hn : 0<n) (hr : 0<r) (loop : CH.Loopless D n)
    (deg : CH.MinOutdegreeAtLeast D n r) (missing : ¬CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r)) :
    CHRuleCatalog.Bad ⟨n,r,D⟩ := ⟨hn,hr,loop,deg,missing⟩

@[aesop safe forward (rule_sets := [CHGraphFamilies])]
theorem parent_cut_exclusion {p} (b : CHRuleCatalog.Bad p) :
    ¬ParentCutFrontier.Gate p.n p.s (CHRuleCatalog.cutoff p) :=
  fun hit=>b.missing (ParentCutFrontier.close b.order b.degree_pos b.loopless b.degree hit)

@[aesop safe forward (rule_sets := [CHGraphFamilies])]
theorem packing_on_input {p} (b : CHRuleCatalog.Bad p) :
    RecursivePackingRules.Laws p.D (range p.n) (CHRuleCatalog.cutoff p) := by
  have hq : 1≤CHRuleCatalog.cutoff p := by
    change 1≤CH.ceilDiv p.n p.s
    by_contra! no
    have : CH.ceilDiv p.n p.s=0 := by omega
    unfold CH.ceilDiv at this
    have rem := Nat.mod_lt (p.n+p.s-1) b.degree_pos
    have div := Nat.mod_add_div (p.n+p.s-1) p.s
    rw [this,Nat.mul_zero] at div
    have := b.order
    have := b.degree_pos
    omega
  exact RecursivePackingRules.on_free hq (qfree_of_noShort b.loopless b.missing)

open Lean Meta Elab Tactic

initialize numericGuard : TagAttribute ←
  registerTagAttribute `ch_numeric_guard "decidable CH family guard with natural-number parameters"

private def visibleCount : TacticM Nat := do
  let lctx := (← (← getMainGoal).getDecl).lctx
  return lctx.foldl (fun n l=>if l.isImplementationDetail then n else n+1) 0

/-- The verdict on a guard computed from its own arguments. It depends on
the guard alone, so sibling families and later rounds reuse it. A proof
found from a family's hypotheses is never stored here. -/
initialize guardVerdicts : IO.Ref (Std.HashMap Expr (Option Expr)) ← IO.mkRef {}

/-- Decide the guard on the actual expressions supplied by the child. An
input record can contain a symbolic digraph even when its order, degree
and cutoff all compute to numerals. Keep the proof of the projection and
the division inside Lean. -/
private def decideNumericGuardOnce (p : Expr) (key : Name) : TacticM (Option Expr) := do
  let args ← liftMetaM (p.getAppArgs.mapM whnfD)
  if args.any (fun x=>x.isFVar || x.isProj) then return none
  let saved ← saveState
  let before ← getGoals
  try
    let test ← mkFreshExprSyntheticOpaqueMVar p
    setGoals [test.mvarId!]
    let guardName := mkIdent key
    -- Division can hide record projections below its head. Reduce those first,
    -- so a symbolic digraph cannot prevent a closed finite test from computing.
    withoutRecover <| evalTactic (← `(tactic| solve
      | (try dsimp only [CHRuleCatalog.cutoff, CH.ceilDiv]); decide
      | norm_num [$guardName:ident, CHRuleCatalog.cutoff, CH.ceilDiv]))
    if (← getGoals).isEmpty then
      let proof ← instantiateMVars test
      setGoals before
      return some proof
  catch err =>
    if err.isInterrupt || err.isRuntime then throw err
  saved.restore
  return none

private def decideNumericGuard (p : Expr) (key : Name) : TacticM (Option Expr) := do
  if (← IO.getEnv "CH_REPLAY_BASELINE").isSome then return ← decideNumericGuardOnce p key
  if let some verdict := (← guardVerdicts.get)[p]? then return verdict
  let verdict ← decideNumericGuardOnce p key
  guardVerdicts.modify (·.insert p verdict)
  return verdict

/-- Equations in the family that pin a natural-number expression to a
numeral, such as a cutoff known to be three. -/
private def pinnedNumbers : TacticM (Array (Expr × Expr)) := withMainContext do
  let mut found := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      let t := (← instantiateMVars d.type).consumeMData
      if let some (ty,lhs,rhs) := t.eq? then
        if ty.isConstOf ``Nat && rhs.nat?.isSome && lhs.nat?.isNone then
          found := found.push (lhs,d.toExpr)
  return found

/-- Compute closed natural-number subterms, such as a field of a recorded
theorem, so that later arithmetic sees numerals. -/
private def computeClosedNumbers (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if x.hasFVar || x.hasMVar || x.hasLooseBVars then return .continue
    if x.nat?.isSome || x.isRawNatLit then return .done x
    unless (← inferType x).isConstOf ``Nat do return .continue
    if let .lit (.natVal k) := (← whnfD x) then return .done (mkNatLit k)
    return .continue)

/-- Decide a guard whose arguments the family itself determines. Rewrite
with the pinned numbers that occur in the guard. Closed parts are then
computed, and the remaining linear parts are proved from the family's
own hypotheses. Nothing is attempted unless some equation applies. -/
private def proveGuardFromFamily (p : Expr) (key : Name) (pins : Array (Expr × Expr)) :
    TacticM (Option Expr) := do
  let relevant := pins.filter fun (lhs,_)=>(p.find? (· == lhs)).isSome
  if relevant.isEmpty then return none
  let saved ← saveState
  let before ← getGoals
  try
    let test ← mkFreshExprSyntheticOpaqueMVar p
    let mut goal := test.mvarId!
    for (lhs,proof) in relevant do
      let target ← instantiateMVars (← goal.getType)
      if (target.find? (· == lhs)).isSome then
        let step ← goal.rewrite target proof
        goal ← goal.replaceTargetEq step.eNew step.eqProof
    goal ← goal.replaceTargetDefEq (← computeClosedNumbers (← instantiateMVars (← goal.getType)))
    setGoals [goal]
    let guardName := mkIdent key
    withoutRecover <| evalTactic (← `(tactic| solve
      | (try dsimp only [CHRuleCatalog.cutoff, CH.ceilDiv]); decide
      | norm_num [$guardName:ident, CHRuleCatalog.cutoff, CH.ceilDiv]
      | (unfold $guardName:ident; (try dsimp only); repeat' apply And.intro) <;>
          first | assumption | decide | omega))
    if (← getGoals).isEmpty then
      let proof ← instantiateMVars test
      setGoals before
      return some proof
  catch err =>
    if err.isInterrupt || err.isRuntime then throw err
  saved.restore
  return none

private def proveNumericGuard (p : Expr) (key : Name) (pins : Array (Expr × Expr) := #[]) :
    TacticM (Option Expr) := do
  if let some proof ← decideNumericGuard p key then return some proof
  proveGuardFromFamily p key pins

/-- A registered forward theorem can leave a numerical guard as its last
premise. When the current graph determines that guard, publish its proof
so both engines may reuse it on the same graph and marks. -/
elab "activate_ch_guards" : tactic => withMainContext do
  let g ← getMainGoal
  let ctx ← getLCtx
  let pins ← pinnedNumbers
  let mut known : Std.HashMap Expr Expr := {}
  let mut considered : Std.HashSet Expr := {}
  for d in ctx do
    unless d.isImplementationDetail do
      known := known.insert (← instantiateMVars d.type).consumeMData d.toExpr
  let mut cursor := g
  for d in ctx do
    unless d.isImplementationDetail do
      let .forallE _ dom body _ := (← instantiateMVars d.type).consumeMData | continue
      if body.consumeMData.isConstOf ``False then continue
      let p := dom.consumeMData
      let some key := p.getAppFn.constName? | continue
      if !(numericGuard.hasTag (← getEnv) key) then continue
      let mut evidence := known.get? p
      if evidence.isNone && !considered.contains p then
        considered := considered.insert p
        if let some proof ← proveNumericGuard p key pins then
          let (_,next) ← cursor.note (← mkFreshUserName `chGuard) proof (some p)
          cursor := next
          known := known.insert p proof
          evidence := some proof
          logInfo m!"CH-FAMILY GUARD {← g.getTag} {p}"
      if let some proof := evidence then
        let conclusion := (body.instantiate1 proof).consumeMData
        unless known.contains conclusion do
          let application := mkApp d.toExpr proof
          let (_,next) ← cursor.note (← mkFreshUserName `chEnabled) application (some conclusion)
          cursor := next
          known := known.insert conclusion application
  replaceMainGoal [cursor]

/-- Close a family when the forward rules have produced incompatible
facts about the same objects. Compare the arguments of a predicate before
considering its definition, so comparing two labels never expands a graph. -/
elab "close_ch_family" : tactic => withMainContext do
  let g ← getMainGoal
  let mut positive : Std.HashMap Name (Array (Expr × Expr)) := {}
  let mut negative : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      let t := (← instantiateMVars d.type).consumeMData
      if t.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) d.toExpr)
        replaceMainGoal []
        return
      if t.isAppOfArity ``Not 1 then
        negative := negative.push (t.appArg!.consumeMData, d.toExpr)
      else if t.isForall && t.bindingBody!.isConstOf ``False then
        negative := negative.push (t.bindingDomain!.consumeMData, d.toExpr)
      else if let some key := t.getAppFn.constName? then
        positive := positive.insert key ((positive.getD key #[]).push (t,d.toExpr))
  for (t,deny) in negative do
    if let some key := t.getAppFn.constName? then
      for (u,proof) in positive.getD key #[] do
        if u.getAppNumArgs == t.getAppNumArgs &&
            (← withReducible <| u.getAppArgs.zip t.getAppArgs |>.allM fun (x,y) => isDefEqGuarded x y) then
          g.assign (← mkFalseElim (← g.getType) (mkApp deny proof))
          replaceMainGoal []
          return
      if numericGuard.hasTag (← getEnv) key then
        if let some proof ← proveNumericGuard t key then
          g.assign (← mkFalseElim (← g.getType) (mkApp deny proof))
          logInfo m!"CH-FORWARD closed at {t}"
          replaceMainGoal []
          return

/-- Existing witness construction and typed rule matching share a fixed
point. Each round can feed new evidence produced by the other registry. -/
elab "drain_ch_graphs" : tactic => withCurrHeartbeats do
  let mut running := true
  while running do
    evalTactic (← `(tactic| drain_ch_witnesses))
    let before ← visibleCount
    evalTactic (← `(tactic| saturate_ch_families))
    let added := (← visibleCount)-before
    logInfo m!"CH-FORWARD ROUND {← (← getMainGoal).getTag} added={added}"
    running := added>0
  evalTactic (← `(tactic| close_ch_family))

end LeanCH.BR.PackingForwardRules
