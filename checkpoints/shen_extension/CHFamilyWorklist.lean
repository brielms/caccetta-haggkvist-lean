import checkpoints.shen_extension.PackingForwardRules
import checkpoints.shen_extension.CHFamilyDeclarations

namespace LeanCH.BR.CHFamilyWorklist
open Lean Meta Elab Tactic

private inductive Opened (P : Prop) : Prop where
  | record

initialize measuredRounds : IO.Ref Nat ← IO.mkRef 0

/-- Local abbreviations name physical sets and rows in many family
conclusions. Expose their case constructors while preserving the
bundled proof. Ordinary named predicates keep their registration policy. -/
private partial def exposeLets (t : Expr) : Expr :=
  match t.consumeMData with
  | .letE _ _ value body _ => exposeLets (body.instantiate1 value)
  | other => other

private def bundled (t : Expr) : Bool :=
  t.isAppOfArity ``Or 2 || t.isAppOfArity ``And 2 || t.isAppOf ``Exists

private def original : IO Bool := return (← IO.getEnv "CH_REPLAY_BASELINE").isSome

private def designatedScan (t : Expr) : MetaM (Option Name) := do
  if let some n := t.getAppFn.constName? then
    if (splitPredicates.getState (← getEnv)).contains n then return some n
  unless bundled t do return none
  for n in splitRules.getState (← getEnv) do
    if ← withoutModifyingMCtx do
      let (_,_,pattern) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels n))
      let pattern := exposeLets pattern
      if pattern.getAppFn != t.getAppFn then return false
      return ← withReducible (isDefEqGuarded pattern t)
    then return some n
  return none

/-- Whether a statement is a designated split depends on the statement and
on the registered patterns, never on the family it sits in. The answer is
kept per statement and discarded when a pattern or predicate is registered. -/
initialize designations : IO.Ref (Nat × Nat × Std.HashMap Expr (Option Name)) ← IO.mkRef (0,0,{})

private def designated (t : Expr) : MetaM (Option Name) := do
  if ← original then return ← designatedScan t
  let env ← getEnv
  let rules := (splitRules.getState env).size
  let predicates := (splitPredicates.getState env).size
  let (r,p,known) ← designations.get
  let known := if r==rules && p==predicates then known else {}
  if let some answer := known[t]? then return answer
  let answer ← designatedScan t
  designations.set (rules,predicates,known.insert t answer)
  return answer

/-- Eliminate constructors on copies of newly derived proofs. The intact
originals can still supply rules that consume the bundled conclusion. -/
private partial def unpack (g : MVarId) (items : List Expr) : TacticM (List MVarId) := g.withContext do
  match items with
  | [] => return [g]
  | h :: rest =>
    if !h.isFVar || !bundled (exposeLets (← inferType h)) then return ← unpack g rest
    let cases ← g.cases h.fvarId!
    let mut goals := []
    for c in cases do
      let remaining := c.fields.toList ++ rest.map c.subst.apply
      goals := goals ++ (← unpack c.mvarId remaining)
    return goals

/-- With CH_REPLAY_TIMING set, report the elapsed time and heartbeats of
each phase of a round. The phases themselves are unchanged. -/
private def timed {α} (phase : String) (g : MVarId) (act : TacticM α) : TacticM α := do
  unless (← IO.getEnv "CH_REPLAY_TIMING").isSome do return ← act
  let ms ← IO.monoMsNow
  let beats ← IO.getNumHeartbeats
  let result ← act
  logInfo m!"CH-TIME {← g.getTag} phase={phase} ms={(← IO.monoMsNow)-ms} kiloheartbeats={((← IO.getNumHeartbeats)-beats)/1000}"
  return result

private def visible (g : MVarId) : MetaM Nat := do
  return (← g.getDecl).lctx.foldl (fun n l=>if l.isImplementationDetail then n else n+1) 0

/-- Run the legacy and the typed rules until neither adds a fact. The typed
rules run to their own fixed point, and so do the legacy rules. A second
pass of either is needed only after the other one added something. In the
original engine that second pass was a whole further round on the same
family, including the guard, closure and split phases. -/
private def settleRules (g : MVarId) (legacy : Bool) : TacticM Unit := do
  let mut typedIsCurrent := false
  repeat
    let before ← visible (← getMainGoal)
    if legacy then timed "legacy" g (evalTactic (← `(tactic| drain_ch_witnesses)))
    if (← visible (← getMainGoal))>before then typedIsCurrent := false
    if typedIsCurrent then break
    let before ← visible (← getMainGoal)
    timed "typed" g (evalTactic (← `(tactic| saturate_ch_families)))
    typedIsCurrent := true
    if !legacy || (← visible (← getMainGoal))==before then break

private def advance (g : MVarId) (legacy : Bool) : TacticM (Bool × List MVarId) := do
  setGoals [g]
  let old := (← g.getDecl).lctx
  let joint := !(← original)
  if joint then settleRules g legacy
  else
    if legacy then timed "legacy" g (evalTactic (← `(tactic| drain_ch_witnesses)))
    timed "typed" g (evalTactic (← `(tactic| saturate_ch_families)))
  let settledCount ← visible (← getMainGoal)
  timed "guards" g (evalTactic (← `(tactic| activate_ch_guards)))
  let current ← getMainGoal
  let afterGuards ← visible current
  timed "close" g (evalTactic (← `(tactic| close_ch_family)))
  if (← getGoals).isEmpty then
    if (← IO.getEnv "CH_REPLAY_DUMP").isSome then logInfo m!"CH-CLOSED {← g.getTag}"
    return (true,[])
  timed "splits" g <| current.withContext do
    let ctx ← getLCtx
    let mut seen : Std.HashSet Expr := {}
    for d in ctx do
      if d.type.isAppOfArity ``Opened 1 then seen := seen.insert d.type.appArg!
    let mut cursor := current
    let mut copies := []
    let mut added := 0
    for d in ctx do
      unless d.isImplementationDetail do
        let t := exposeLets (← instantiateMVars d.type)
        let fresh := !old.contains d.fvarId
        if fresh then added := added+1
        let marked := t.isAppOfArity ``Branch 1
        let producer ← if marked then pure none else designated t
        if marked || producer.isSome then
          let p := if marked then t.appArg! else t
          let shape ← if bundled p then pure p else whnf p
          unless seen.contains shape do
            seen := seen.insert shape
            let proof ← if marked then mkAppM ``Branch.evidence #[d.toExpr] else pure d.toExpr
            let (_,recorded) ← cursor.note (← mkFreshUserName `chOpened) (mkApp (mkConst ``Opened.record) shape)
            unless bundled shape do throwError "designated family has no case constructors: {p}"
            let (fid,next) ← recorded.note (← mkFreshUserName `chEvidence) proof (some shape)
            cursor := next
            copies := mkFVar fid :: copies
            logInfo m!"CH-FAMILY OPEN {← current.getTag} producer={producer.getD `explicit} alternatives={p}"
    let children ← unpack cursor copies.reverse
    logInfo m!"CH-FAMILY ROUND {← current.getTag} added={added} expanded={copies.length} children={children.length}"
    -- With the joint fixed point above, a family needs another round only
    -- when a guard or a split gave the rules something new to read.
    let again := if joint then afterGuards>settledCount || !copies.isEmpty else added>0 || !copies.isEmpty
    return (again,children)

/-- Report propositions supported only on the numerical input and its
natural-number abbreviations. Graph-dependent hypotheses stay in Lean's
full context dump. This is a view of the settled goal, never a pruning rule. -/
private def reportNumbers (g : MVarId) : TacticM Unit := g.withContext do
  let ctx ← getLCtx
  let mut allowed : FVarIdSet := {}
  -- The cutoff declaration determines the numerical parameters even when
  -- the names which introduced them carry different macro scopes.
  for d in ctx do
    if let some v := d.value? (allowNondep := true) then
      let v := (← instantiateMVars v).consumeMData
      if v.isAppOfArity `CH.ceilDiv 2 then
        let args := v.getAppArgs
        if args.all Expr.isFVar then
          for x in args do allowed := allowed.insert x.fvarId!
          allowed := allowed.insert d.fvarId
  if allowed.isEmpty then return
  for d in ctx do
    unless d.isImplementationDetail do
      if let some val := d.value? (allowNondep := true) then
        if (← instantiateMVars d.type).isConstOf ``Nat && (collectFVars {} (← instantiateMVars val)).fvarIds.all allowed.contains then
          allowed := allowed.insert d.fvarId
      let t := exposeLets (← instantiateMVars d.type)
      if t.hasFVar then
        let deps := (collectFVars {} t).fvarIds
        if !deps.isEmpty && deps.all allowed.contains && (← isProp t) then
          logInfo m!"CH-NUMERIC {← g.getTag} {d.userName} : {t}"

/-- Bounds on one replay. The canonical root settles in about twenty rounds
on any one line of descent and under two hundred queued cases. -/
private def roundLimit : Nat := 256
private def queueLimit : Nat := 4096

/-- Breadth-first on proof obligations. A revisited fact keeps its old
labels, while a different instantiation can put the same rule back to work. -/
private def run (legacy : Bool) : TacticM Unit := withCurrHeartbeats do
  let mut pending : Array (MVarId × Nat) := (← getGoals).toArray.map fun g=>(g,0)
  let mut settled := #[]
  let mut i := 0
  while i<pending.size do
    let (g,rounds) := pending[i]!
    i := i+1
    unless ← g.isAssigned do
      if let some limit := (← IO.getEnv "CH_REPLAY_ROUNDS").bind String.toNat? then
        if (← measuredRounds.get)≥limit then throwError "CH-MEASURE already stopped"
      let (again,children) ← advance g legacy
      -- Measurement only: CH_REPLAY_LINEAGE follows the first case of every split to its end
      -- and gives up the others, so one complete line of descent can be timed and compared.
      let children ← if (← IO.getEnv "CH_REPLAY_LINEAGE").isSome then do
          for c in children.drop 1 do c.admit
          pure (children.take 1)
        else pure children
      -- Measurement only: CH_REPLAY_ROUNDS=k stops after k rounds and prints the cases reached.
      if let some limit := (← IO.getEnv "CH_REPLAY_ROUNDS").bind String.toNat? then
        let seen ← measuredRounds.modifyGet fun k=>(k+1,k+1)
        if (← IO.getEnv "CH_REPLAY_DUMP").isSome || seen≥limit then
          for c in children do logInfo m!"CH-MEASURE CASE round={seen}
{MessageData.ofGoal c}"
        if seen≥limit then throwError "CH-MEASURE stopped after {seen} rounds"
      if again then
        -- A rule that names a new witness every round never settles. Report
        -- the unfinished queue instead of running out of time.
        if rounds≥roundLimit || pending.size≥queueLimit then
          throwError "CH-FAMILY UNFINISHED {← g.getTag}: after {rounds} successive rounds and {pending.size} queued cases, replay still adds facts or cases. Some rule may name a fresh witness on every application."
        pending := pending ++ children.toArray.map fun c=>(c,rounds+1)
      else settled := settled ++ children.toArray
  if legacy then for g in settled do reportNumbers g
  if (← IO.getEnv "CH_REPLAY_DUMP").isSome then
    for g in settled do logInfo m!"CH-SETTLED {← g.getTag}\n{MessageData.ofGoal g}"
  setGoals settled.toList

elab "replay_ch_families" : tactic => run true
elab "replay_ch_typed_families" : tactic => run false

end LeanCH.BR.CHFamilyWorklist
