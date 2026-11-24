import Aesop

declare_aesop_rule_sets [CHGraphFamilies]

namespace LeanCH.BR.CHForwardCatalog
open Lean Meta Elab Tactic Aesop
open Batteries (BinomialHeap)

private abbrev Queue := BinomialHeap ForwardRuleMatch ForwardRuleMatch.le

/-- Work done by one saturation, reported with CH_REPLAY_TIMING. -/
private structure Tally where
  visited : Nat := 0
  remembered : Nat := 0
  verbatim : Nat := 0
  reducible : Nat := 0
  added : Nat := 0
  proofMs : Nat := 0
  compareMs : Nat := 0
  stateMs : Nat := 0

/-- A complete match is a rule with its instantiation. Its conclusion is a
function of those two, so the statement found once is the statement found
on every later visit to the same match. -/
private abbrev MatchKey := Name × Array (Option Expr) × Array (Option Level)

initialize conclusions : IO.Ref (Std.HashMap MatchKey Expr) ← IO.mkRef {}

private def matchKey (m : ForwardRuleMatch) : MatchKey :=
  let (args,levels) := m.match.reconstructArgs m.rule
  (m.rule.name.name,args,levels)

/-- Apply a complete match exactly as Aesop's `ForwardRuleMatch.apply` does
with `skipExistingProps`. Aesop compares the new statement with every
hypothesis up to reducible unfolding. A statement that is present word for
word passes that test at once, so it is looked up in a table first. Every
other statement still goes through Aesop's own comparison. -/
private def applyMatch (goal : MVarId) (m : ForwardRuleMatch) (known : Std.HashSet Expr)
    (tally : Tally) : ScriptT BaseM (Option (MVarId × FVarId × Array FVarId × Expr) × Tally) :=
  goal.withContext do
    let tally := { tally with visited := tally.visited+1 }
    let key := matchKey m
    if let some statement := (← conclusions.get)[key]? then
      if known.contains statement then return (none,{ tally with remembered := tally.remembered+1 })
    let t0 ← IO.monoMsNow
    let some prf ← m.getProof goal | return (none,tally)
    let type ← inferType prf
    let statement ← instantiateMVars type
    conclusions.modify (·.insert key statement)
    let t1 ← IO.monoMsNow
    let tally := { tally with proofMs := tally.proofMs+(t1-t0) }
    if known.contains statement then return (none,{ tally with verbatim := tally.verbatim+1 })
    let redundant ← isHypRedundantReducibleRigid type
    let tally := { tally with compareMs := tally.compareMs+((← IO.monoMsNow)-t1) }
    if redundant then return (none,{ tally with reducible := tally.reducible+1 })
    let name ← getUnusedUserName forwardHypPrefix
    let hyp := { userName := name, value := prf, type }
    let (goal, #[hyp]) ← assertHypothesisS goal hyp (md := .default)
      | throwError "saturate: asserting one hypothesis returned a different number"
    let tally := { tally with added := tally.added+1 }
    if ! m.rule.destruct then
      return (some (goal,hyp,#[],statement),tally)
    let usedPropHyps ← goal.withContext m.getPropHyps
    let (goal,_) ← tryClearManyS goal usedPropHyps
    return (some (goal,hyp,usedPropHyps,statement),tally)

/-- Aesop's stateful saturation loop with the lookup above. The queue, the
forward state and the order of applications are Aesop's. -/
private partial def saturateIndexed (rs : LocalRuleSet) (goal : MVarId) : ScriptT BaseM (MVarId × Tally) :=
  goal.withContext do
    goal.checkNotAssigned `saturate
    let t0 ← IO.monoMsNow
    let mut known : Std.HashSet Expr := {}
    for d in ← getLCtx do
      unless d.isImplementationDetail do known := known.insert (← instantiateMVars d.type)
    let mut queue : Queue := ∅
    -- Aesop's `mkInitialForwardState` enqueues one hypothesis at a time into
    -- a shared rule state, which copies that rule's queue on every step. Here
    -- the hypotheses are grouped by rule first and each rule state is filled
    -- while it has a single owner. The rule states, the queues inside them
    -- and the hypothesis map come out the same.
    let mut slot : Std.HashMap RuleName Nat := {}
    let mut groups : Array (ForwardRule × Array (FVarId × PremiseIndex)) := #[]
    let mut hyps : PHashMap FVarId (PArray (RuleName × PremiseIndex)) := {}
    let mut patterned : Array (FVarId × Array (ForwardRule × Substitution)) := #[]
    let mut indexMs := 0
    let mut patternMs := 0
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      let a ← IO.monoMsNow
      let rules ← rs.applicableForwardRules ldecl.type
      let b ← IO.monoMsNow
      let patInsts ← rs.forwardRulePatternSubstsInLocalDecl ldecl
      indexMs := indexMs+(b-a)
      patternMs := patternMs+((← IO.monoMsNow)-b)
      for (r,i) in rules do
        match slot[r.name]? with
        | some k => groups := groups.modify k fun (rule,items)=>(rule,items.push (ldecl.fvarId,i))
        | none =>
          slot := slot.insert r.name groups.size
          groups := groups.push (r,#[(ldecl.fvarId,i)])
      unless rules.isEmpty do
        hyps := hyps.insert ldecl.fvarId (rules.map fun (r,i)=>(r.name,i)).toPArray'
      unless patInsts.isEmpty do patterned := patterned.push (ldecl.fvarId,patInsts)
    let c ← IO.monoMsNow
    let mut ruleStates : PHashMap RuleName RuleState := {}
    for (r,items) in groups do
      let mut state := r.initialRuleState
      for (h,i) in items do state := state.enqueueRawHyp (.fvarId h) i
      ruleStates := ruleStates.insert r.name state
    let mut fs : ForwardState := { ruleStates, hyps, patSubsts := {} }
    for (h,patInsts) in patterned do fs := fs.enqueuePatSubsts (.hyp h) patInsts
    let enqueueMs := (← IO.monoMsNow)-c
    let patInsts ← rs.forwardRulePatternSubstsInExpr (← goal.getType)
    fs := fs.enqueueTargetPatSubsts patInsts
    for m in rs.constForwardRuleMatches do queue := queue.insert m
    let u ← IO.monoMsNow
    let (ready,ruleMatches) ← fs.update goal (phase? := none)
    let updateMs := (← IO.monoMsNow)-u
    for m in ruleMatches do queue := queue.insert m
    if (← IO.getEnv "CH_REPLAY_TIMING").isSome then
      logInfo m!"CH-TYPED-STATE {← goal.getTag} indexMs={indexMs} patternMs={patternMs} enqueueMs={enqueueMs} updateMs={updateMs} initialMatches={ruleMatches.size}"
    go ready queue ∅ known goal { stateMs := (← IO.monoMsNow)-t0 }
where
  go (fs : ForwardState) (queue : Queue) (erasedHyps : Std.HashSet FVarId)
      (known : Std.HashSet Expr) (goal : MVarId) (tally : Tally) : ScriptT BaseM (MVarId × Tally) := do
    checkSystem "saturate"
    goal.withContext do
      let some (m,queue) := queue.deleteMin | return (goal,tally)
      if m.rule.name.phase == .unsafe || m.anyHyp erasedHyps.contains then
        return ← go fs queue erasedHyps known goal tally
      let (result,tally) ← applyMatch goal m known tally
      let some (goal,hyp,removedHyps,statement) := result
        | return ← go fs queue erasedHyps known goal tally
      goal.withContext do
        let t0 ← IO.monoMsNow
        let fs := removedHyps.foldl (init := fs) fun fs h => fs.eraseHyp h
        let erasedHyps := erasedHyps.insertMany removedHyps
        let type ← hyp.getType
        let rules ← rs.applicableForwardRules type
        let patInsts ← rs.forwardRulePatternSubstsInLocalDecl (← hyp.getDecl)
        let fs := fs.enqueueHypWithPatSubsts hyp rules patInsts
        let (fs,ruleMatches) ← fs.update goal (phase? := none)
        let queue := ruleMatches.foldl (init := queue) fun queue m => queue.insert m
        go fs queue erasedHyps (known.insert statement) goal
          { tally with stateMs := tally.stateMs+((← IO.monoMsNow)-t0) }

/-- Saturate precisely the registered graph rules. The Aesop forward index
matches by type and term, so distinct instances of a rule can fire on
different labels in the same context. No depth cutoff is supplied.

With CH_REPLAY_BASELINE set this calls `Aesop.saturate` unchanged. -/
elab "saturate_ch_families" : tactic => withCurrHeartbeats do
  let options ← Aesop.Frontend.mkForwardOptions none false
  let sets ← Aesop.Frontend.getGlobalRuleSets #[`CHGraphFamilies]
  let rules ← Aesop.mkLocalRuleSet sets options
  let original := (← IO.getEnv "CH_REPLAY_BASELINE").isSome ||
    !(aesop.dev.statefulForward.get (← getOptions))
  liftMetaTactic fun g=>do
    let prior := (← g.getDecl).lctx
    let next ← if original then pure (← Aesop.saturate rules g options).1 else do
      let (((next,tally),_),_) ← (saturateIndexed rules g).run.run
      if (← IO.getEnv "CH_REPLAY_TIMING").isSome then
        logInfo m!"CH-TYPED {← g.getTag} matches={tally.visited} remembered={tally.remembered} verbatim={tally.verbatim} reducible={tally.reducible} added={tally.added} proofMs={tally.proofMs} compareMs={tally.compareMs} stateMs={tally.stateMs}"
      pure next
    let finalCtx := (← next.getDecl).lctx
    for l in finalCtx do
      unless l.isImplementationDetail || prior.contains l.fvarId do
        logInfo m!"CH-FORWARD {← g.getTag} {l.type}"
    pure [next]
end LeanCH.BR.CHForwardCatalog
