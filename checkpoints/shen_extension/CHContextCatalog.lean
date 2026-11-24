import Lean

/-! Run the capstone's named witness constructions on its actual local contexts.
The parser takes the rule bodies directly from the root proof. An existential is
opened by the original Lean tactic, so graph, price and witness parameters stay linked. -/
namespace LeanCH.BR.CHContextCatalog
open Lean Meta Elab Tactic

private structure Entry where
  text : String
  term : Syntax
  outputs : Array Name
  premise : Option Name
  inputs : Array Name
  trigger : Option (Name × Name)
  deriving Inhabited

initialize registerTraceClass `CH.catalog

private structure LocalStore (α : Type) where
  ext : EnvExtension α
  deriving Inhabited

private def LocalStore.get [Monad m] [MonadEnv m] [Inhabited α] (s : LocalStore α) : m α :=
  return s.ext.getState (← getEnv)
private def LocalStore.set [MonadEnv m] [Inhabited α] (s : LocalStore α) (v : α) : m Unit :=
  modifyEnv (s.ext.setState · v)
private def LocalStore.modify [MonadEnv m] [Inhabited α] (s : LocalStore α) (f : α→α) : m Unit :=
  modifyEnv (s.ext.modifyState · f)
private def localStore [Inhabited α] (v : α) : IO (LocalStore α) := do
  return ⟨← registerEnvExtension (pure v) (asyncMode := .local)⟩

private initialize registered : LocalStore (Array Entry) ← localStore #[]
private initialize guardNames : LocalStore (Array Name) ← localStore #[]
private initialize manifest : LocalStore (Array String) ← localStore #[]
private initialize sites : LocalStore (Std.HashMap (Nat × Nat × Name) Nat) ← localStore {}
private initialize instances : LocalStore (Std.HashMap (Nat × Array Expr) Nat) ← localStore {}
private initialize usedRoles : LocalStore (Std.HashMap Nat (Array Name)) ← localStore {}

/-- An engine receipt. The proof lives in this branch, so rollback and sibling
cases cannot inherit a success that did not take place in their context. -/
private inductive Fired (key : Nat) : Prop where
  | record

private inductive Binding (role : String) {α : Sort u} (value : α) : Prop where
  | record

private abbrev View := Array (Name × Expr)

private abbrev Lookup := Name → Option LocalDecl

/-- Match `findFromUserName?`: in declaration order the last binding wins.
Rebuild after each successful tactic, since it can also erase or rename locals. -/
private def nameTable (ctx : LocalContext) : Std.HashMap Name LocalDecl := Id.run do
  let mut names : Std.HashMap Name LocalDecl := {}
  for d in ctx do names := names.insert d.userName d
  return names

/-- Look a name up in a table that has already been built. Written as
`indexed (nameTable ctx)` at each use: a definition that takes the context
and returns the lookup function would rebuild the table for every name. -/
private def indexed (names : Std.HashMap Name LocalDecl) : Lookup := fun n => names[n]?

/-- The lookup as first written, kept for before-and-after measurements
with CH_REPLAY_BASELINE. It returns the same answers and rebuilds the
table on every call. -/
private def rebuiltLookup (ctx : LocalContext) : Lookup := Id.run do
  let mut names : Std.HashMap Name LocalDecl := {}
  for d in ctx do names := names.insert d.userName d
  return fun n => names[n]?

private def lookupFor (slow : Bool) (ctx : LocalContext) : IO Lookup :=
  if slow then pure (rebuiltLookup ctx) else do
    let names := nameTable ctx
    pure (indexed names)

syntax "ch_on_fact " ident " of " ident " => " tactic : tactic

private def journal (line : String) : TacticM Unit := do
  if let some path ← IO.getEnv "CH_CATALOG_TRACE_FILE" then
    IO.FS.withFile path .append fun h => h.putStrLn line

private def words (s : String) := (s.splitOn "\n").flatMap (fun l =>
  ((l.map (fun c => if c.isAlphanum || c=='_' || c=='\'' then c else ' ')).splitOn " ").filter (·!=""))

private def outputNames (s : String) : Array Name := Id.run do
  let head := (s.splitOn ":=").head!
  let pattern := if s.startsWith "obtain " then (head.splitOn " : ").head! else head
  let ws := words pattern
  if s.startsWith "obtain " then
    if head.contains "rfl" || head.contains "|" then return #[]
    return ((ws.drop 1).filter (fun n => n != "_")).toArray.map Name.mkSimple
  if s.startsWith "have " || s.startsWith "let " then
    if let some n := ws[1]? then return #[Name.mkSimple n]
  return #[]

/-- Apply a branch-specific rule only in a context that actually has its premise. -/
elab (name := ifCHFact) "if_ch_fact " key:ident " => " body:tacticSeq : tactic => withMainContext do
  if ((← getLCtx).findFromUserName? key.getId).isSome then evalTactic body

/-- A checked descent can discharge a whole family. Keep its former witness
constructions in the registry for other families where they still apply. -/
elab "prefer_ch_descent " proof:term " retaining " fallback:tacticSeq : tactic => do
  evalTactic (← `(tactic| first | exact $proof | $fallback))

private partial def collect (stx : Syntax) (fm : FileMap) (premise : Option Name := none)
    (trigger : Option (Name × Name) := none) : TacticM Unit := do
  if let `(tactic| ch_on_fact $h:ident of $family:ident => $body:tactic) := stx then
    let head ← resolveGlobalConstNoOverload family
    collect body fm premise (some (h.getId,head))
    return
  if let `(tactic| prefer_ch_descent $p:term retaining $fallback:tacticSeq) := stx then
    let _ := p
    collect fallback fm premise
    return
  if let `(tactic| if_ch_fact $key:ident => $body:tacticSeq) := stx then
    collect body fm (some key.getId)
    return
  let kind := stx.getKind.toString
  if kind.contains "tacticSeq" || stx.getKind == nullKind || kind.endsWith ".cdot" ||
      kind.endsWith ".case" || kind.endsWith ".case'" || kind.endsWith ".allGoals" then
    for child in stx.getArgs do collect child fm premise
    return
  let some p := stx.getPos? | return
  let some e := stx.getTailPos? | return
  let s := (String.Pos.Raw.extract fm.source p e).trimAscii.toString
  let line := (fm.toPosition p).line
  if s.startsWith "by_cases " then
    if let some key := (words s)[1]? then guardNames.modify (·.push (Name.mkSimple key))
  if !s.isEmpty && !stx.isAtom then
    manifest.modify (·.push s!"{line} {((s.splitOn "\n").head!).take 150}")
  let names := outputNames s
  if names.isEmpty then return
  let norm := String.intercalate " " (s.splitOn "\n" |>.map (fun x=>x.trimAscii.toString))
  let all ← registered.get
  let idx := (all.findIdx? (fun r => r.text==norm && r.premise==premise && r.trigger==trigger)).getD all.size
  if idx==all.size then
    let refs := (words norm).eraseDups.toArray.map Name.mkSimple
    let refs := refs.filter (fun n => !names.contains n && !(trigger.any (fun p=>p.1==n)))
    registered.modify (·.push ⟨norm,stx,names,premise,refs,trigger⟩)
  sites.modify (·.insert (p.byteIdx,e.byteIdx,stx.getKind) idx)

private def inputRoles (i : Nat) (r : Entry) : MetaM (Array Name) := do
  return (← usedRoles.get)[i]?.getD r.inputs

/-- After checking a recipe, the kernel expression identifies its free inputs.
Bound row names and field names such as the D in X.D do not create instances. -/
private def learnRoles (i : Nat) (r : Entry) (lookup : Lookup) (before : MVarId)
    (view : View := #[]) : MetaM Unit := do
  if (← usedRoles.get).contains i then return
  let term ← instantiateMVars (mkMVar before)
  let used := (collectFVars {} term).fvarSet
  let roles := r.inputs.filter fun name =>
    if let some (_,v) := view.find? (·.1==name) then v.isFVar && used.contains v.fvarId!
    else (lookup name).any fun d=>used.contains d.fvarId
  usedRoles.modify (·.insert i roles)

/-- The statements that identify an instance are a function of the values
bound to its roles. Remember them per binding. The instance table itself is
consulted exactly as before, so every instance keeps its own number. -/
initialize instanceSignatures :
    IO.Ref (Std.HashMap (Nat × Array Name × Array (Option Expr) × Option Expr) (Array Expr)) ← IO.mkRef {}

private def original : IO Bool := return (← IO.getEnv "CH_REPLAY_BASELINE").isSome

private def keyFor (i : Nat) (r : Entry) (lookup : Lookup) (anchor : Option Expr)
    (view : View := #[]) : MetaM Nat := do
  let roles := (← inputRoles i r) ++ r.premise.toList.toArray
  let values := roles.map fun n=>(view.find? (·.1==n)).map Prod.snd <|> (lookup n).map LocalDecl.toExpr
  let signature := (i,roles,values,anchor)
  let remembered ← if ← original then pure none else pure (← instanceSignatures.get)[signature]?
  let xs ← match remembered with
    | some xs => pure xs
    | none => do
      let mut xs := #[]
      for val in values do
        if let some v := val then
          let ty ← instantiateMVars (← inferType v)
          xs := xs.push (if ← isProp ty then ty else v)
      if let some h := anchor then xs := xs.push (← instantiateMVars (← inferType h))
      instanceSignatures.modify (·.insert signature xs)
      pure xs
  let table ← instances.get
  if let some id := table[(i,xs)]? then return id
  let id := table.size
  instances.modify (·.insert (i,xs) id)
  return id

private def stamp (g : MVarId) (k : Nat) : MetaM MVarId := do
  let arg := mkRawNatLit k
  let (_,g) ← g.note (← mkFreshUserName `chFired) (mkApp (mkConst ``Fired.record) arg)
    (some (mkApp (mkConst ``Fired) arg))
  return g

private def receipts (ctx : LocalContext) : Std.HashSet Nat := Id.run do
  let mut out := {}
  for d in ctx do
    if d.type.isAppOfArity ``Fired 1 then
      if let some n := d.type.appArg!.rawNatLit? then out := out.insert n
  return out

/-- Record ordinary hand-written calls as actual applications. A later output
with the same name on a different carrier cannot masquerade as this receipt. -/
elab "ch_record_call " i:num body:tactic : tactic => withMainContext do
  let id := i.getNat
  let r := (← registered.get)[id]!
  let ctx ← getLCtx
  let before ← getMainGoal
  evalTactic body
  learnRoles id r ctx.findFromUserName? before
  let k ← keyFor id r ctx.findFromUserName? none
  let gs ← getGoals
  setGoals (← gs.mapM fun g => g.withContext do stamp g k)

private partial def instrument (stx : Syntax) : TacticM Syntax := do
  if let `(tactic| ch_on_fact $_h:ident of $_f:ident => $_body:tactic) := stx then return stx
  if let some p := stx.getPos? then
    if let some e := stx.getTailPos? then
      if let some i := (← sites.get)[(p.byteIdx,e.byteIdx,stx.getKind)]? then
        let body : TSyntax `tactic := ⟨stx⟩
        return (← `(tactic| ch_record_call $(quote i):num $body:tactic)).raw
  if stx.isOfKind nullKind || stx.getKind.toString.contains "tacticSeq" ||
      stx.getKind.toString.endsWith ".cdot" || stx.getKind.toString.endsWith ".allGoals" ||
      stx.getKind.toString.endsWith ".case" || stx.getKind.toString.endsWith ".case'" ||
      stx.isOfKind ``ifCHFact || stx.getKind.toString.contains "prefer_ch_descent" then
    return stx.setArgs (← stx.getArgs.mapM instrument)
  return stx

elab "with_ch_root_catalog" steps:tacticSeq : tactic => do
  registered.set #[]
  guardNames.set #[]
  manifest.set #[]
  sites.set {}
  instances.set {}
  usedRoles.set {}
  collect steps (← getFileMap)
  journal s!"registered {(← registered.get).size} constructions, {(← manifest.get).size} source tactics"
  for r in ← registered.get do journal s!"rule {r.outputs} | {r.text}"
  logInfo m!"CH-CATALOG registered {(← registered.get).size} named constructions; {(← manifest.get).size} source tactics"
  evalTactic (← instrument steps)

private def firstLine (s : String) : String := (((s.splitOn "\n").head!).take 180).toString

private partial def boundTerm (n : Name) (bindings : Std.HashMap Name Syntax) : TacticM (Option Syntax) := do
  if let some t := bindings[n]? then return some t
  let .str parent field := n | return none
  let some base ← boundTerm parent bindings | return none
  let lhs : TSyntax `term := ⟨base⟩
  let f := mkIdent (Name.mkSimple field)
  return some (← `(term| ($lhs).$f:ident)).raw

private partial def substituteNames (stx : Syntax) (bindings : Std.HashMap Name Syntax) : TacticM Syntax := do
  if bindings.isEmpty then return stx
  if stx.isIdent then
    if let some t ← boundTerm stx.getId bindings then return t
  if stx.getNumArgs==0 then return stx
  return stx.setArgs (← stx.getArgs.mapM (substituteNames · bindings))

private def roleIndex (ctx : LocalContext) : Std.HashMap Name (Array Expr) := Id.run do
  let mut idx := {}
  for d in ctx do
    if d.type.isAppOfArity ``Binding 3 then
      let args := d.type.getAppArgs
      if let .lit (.strVal role) := args[0]! then
        let n := Name.mkSimple role
        idx := idx.insert n ((idx.getD n #[]).push args[2]!)
  return idx

private def views (r : Entry) (inputs : Array Name) (idx : Std.HashMap Name (Array Expr)) : Array View := Id.run do
  let mut found := #[#[]]
  for n in (inputs ++ r.premise.toList.toArray).toList.eraseDups do
    if let some values := idx[n]? then
      let original := found
      for value in values do found := found ++ original.map (·.push (n,value))
  return found

/-- A proof of Boundary X F L stays attached to its actual L. Eliminate
incompatible mixed tuples by dependency before elaborating the recipe. -/
private def coherent (lookup : Lookup) (reads : Array Name) (view : View) : MetaM Bool := do
  if view.isEmpty then return true
  let mut froms := #[]
  let mut tos := #[]
  for (role,v) in view do
    if let some d := lookup role then
      froms := froms.push d.toExpr
      tos := tos.push v
  for n in reads do
    if let some d := lookup n then
      let ty ← instantiateMVars d.type
      let expected := ty.replaceFVars froms tos
      if expected != ty then
        -- An implicit graph or mark might change too. Leave those cases
        -- to full elaboration instead of fixing an unbound parameter here.
        unless (collectFVars {} ty).fvarIds.all (fun id =>
          reads.any fun role => (lookup role).any (·.fvarId==id)) do continue
        let val := ((view.find? (·.1==n)).map Prod.snd).getD d.toExpr
        let actual ← instantiateMVars (← inferType val)
        unless expected==actual || (← withReducible (isDefEqGuarded expected actual)) do return false
  return true

private def choices (r : Entry) (ctx : LocalContext) : MetaM (Array (Option Expr)) := do
  let some (_,pred) := r.trigger | return #[none]
  let mut xs := #[]
  for d in ctx do
    if !d.isImplementationDetail && (← instantiateMVars d.type).consumeMData.getAppFn.constName? == some pred then
      xs := xs.push (some d.toExpr)
  return xs

/-- Every identifier written in a recipe, with the components of dotted names. -/
private partial def identifiers (stx : Syntax) (acc : NameSet := {}) : NameSet :=
  match stx with
  | .ident _ _ n _ => n.components.foldl (fun a c=>a.insert c) (acc.insert n)
  | .node _ _ args => args.foldl (fun a x=>identifiers x a) acc
  | _ => acc

private partial def leadingAtom : Syntax → Option String
  | .atom _ v => some v.trimAscii.toString
  | .node _ _ args => args.findSome? leadingAtom
  | _ => none

private def isClearExcept (stx : Syntax) : Bool :=
  let atoms := (stx.getArgs.filterMap fun a=>match a with
    | .atom _ v => some v.trimAscii.toString
    | _ => none)
  atoms.size≥3 && atoms[0]! == "clear" && atoms[1]! == "*" && atoms[2]! == "-"

/-- Tactics whose effect is determined by the hypotheses they name. -/
private def namedTactics : List String :=
  ["have","obtain","exact","rw","change","show","dsimp","unfold","intro","rintro","refine",
   "apply","constructor","specialize","clear","rcases","let"]

mutual
/-- Can a tactic sequence read a hypothesis that the recipe does not name?
After `clear * - h₁ … hₙ` the rest of the sequence, nested blocks included,
sees only the named hypotheses and what they depend on. Before that point
only tactics from `namedTactics` are trusted. Anything else counts as a
reader, and the recipe keeps the exhaustive retry. -/
private partial def sequenceReads (items : Array Syntax) : Bool := Id.run do
  for item in items do
    match item with
    | .atom .. => continue
    | .missing => continue
    | .node _ kind args =>
      if kind == nullKind then
        -- a separated list of tactics: scan in order, stopping at the clear
        let mut cleared := false
        for sub in args do
          if cleared then break
          match sub with
          | .node _ _ inner =>
            if inner.isEmpty then continue   -- an absent separator
            if isClearExcept sub then cleared := true
            else if tacticReads sub then return true
          | _ => continue
        if cleared then return false
      else if args.isEmpty then continue
      else if isClearExcept item then return false
      else if tacticReads item then return true
    | _ => return true
  return false

private partial def tacticReads (tac : Syntax) : Bool :=
  match leadingAtom tac with
  | some word => if namedTactics.contains word then nestedReads tac else true
  | none => true

/-- Tactic blocks nested inside a trusted tactic or a term. -/
private partial def nestedReads (stx : Syntax) : Bool :=
  match stx with
  | .atom _ v => v.trimAscii.toString == "‹"
  | .node _ kind args =>
    if kind.toString.contains "tacticSeq" then sequenceReads args
    else args.any nestedReads
  | _ => false
end

/-- A recipe is indexed by the names it reads when no tactic in it can read
an unnamed hypothesis. Its failure then depends only on what those names
are bound to. -/
private def namedDependencies (r : Entry) : Option (Array Name) :=
  if tacticReads r.term then none else some (identifiers r.term).toArray

initialize recipeDependencies : IO.Ref (Std.HashMap String (Option (Array Name))) ← IO.mkRef {}

private def dependenciesOf (r : Entry) : IO (Option (Array Name)) := do
  if let some known := (← recipeDependencies.get)[r.text]? then return known
  let deps := namedDependencies r
  recipeDependencies.modify (·.insert r.text deps)
  return deps

/-- Failed attempts of indexed recipes: the rule, its trigger and view, and
the binding of every name it reads. An attempt with the same entry fails
again in the same way, so it is not repeated. A new binding for any of the
names gives a different entry and the recipe is tried again. -/
initialize failedAttempts :
    IO.Ref (Std.HashMap (Nat × Option Expr × Array (Name × Expr) × Array (Option FVarId)) String) ← IO.mkRef {}

/-- A failure has no receipt. The same rule and marks are eligible as soon
as more proof evidence arrives. A successful application gets its own names. -/
private def tryInstance (idx : Nat) (r : Entry) (anchor : Option Expr)
    (done : Std.HashSet Nat) (lookup : Lookup) (view : View := #[]) : TacticM (Option Nat × Option String) := withMainContext do
  unless ← coherent lookup (← inputRoles idx r) view do return (none,none)
  let k ← keyFor idx r lookup anchor view
  if done.contains k then return (none,none)
  if let some p := r.premise then
    if (lookup p).isNone && !(view.any (·.1==p)) then return (none,some s!"missing {p}")
  let attempt ← if ← original then pure none else do
    match ← dependenciesOf r with
    | none => pure none
    | some names => pure (some (idx,anchor,view,names.map fun n=>(lookup n).map (·.fvarId)))
  if let some entry := attempt then
    if let some why := (← failedAttempts.get)[entry]? then return (none,some s!"missing new evidence ({why})")
  let initial := (← getThe Core.State).messages
  let saved ← Tactic.saveState
  try
    let before ← getMainGoal
    let mut bindings : Std.HashMap Name Syntax := {}
    for (role,v) in view do bindings := bindings.insert role (← Term.exprToSyntax v).raw
    if let some (role,_) := r.trigger then
      let some h := anchor | throwError "missing typed trigger"
      bindings := bindings.insert role (← Term.exprToSyntax h).raw
    let mut names := #[]
    for out in r.outputs do
      if (lookup out).isSome then
        let fresh ← mkFreshUserName out
        names := names.push fresh
        bindings := bindings.insert out (mkIdent fresh)
      else names := names.push out
    let body ← substituteNames r.term bindings
    Term.withoutErrToSorry (withoutRecover (evalTactic body))
    let [outputGoal] ← getGoals | throwError "construction changed the number of goals"
    let mut g := outputGoal
    let newctx := (← g.getDecl).lctx
    unless names.all (fun n=>(newctx.findFromUserName? n).isSome) do
      throwError "construction did not bind every result"
    if (← getThe Core.State).messages.toList.countP (·.severity == .error) >
        initial.toList.countP (·.severity == .error) then
      throwError "elaboration reported an error"
    learnRoles idx r lookup before view
    let k ← keyFor idx r lookup anchor view
    for (role,name) in r.outputs.zip names do
      if role != name then
        let val := (newctx.findFromUserName? name).get!.toExpr
        g ← g.withContext do
          let ty ← instantiateMVars (← inferType val)
          if ← isProp ty then
            if let some first := lookup role then
              if (← instantiateMVars first.type)==ty then return g
          let marker ← mkAppOptM ``Binding.record #[some (toExpr role.toString),none,some val]
          return (← g.note (← mkFreshUserName `chBinding) marker).2
    let detail ← match anchor with
      | some h => pure (← ppExpr (← inferType h)).pretty
      | none => pure (String.intercalate ", " ((← inputRoles idx r).toList.filterMap fun n=>do
          let d ← lookup n
          pure s!"{d.userName}"))
    let changed ← view.mapM fun (n,v)=>do return s!"{n}={(← ppExpr v).pretty}"
    let label := s!"rule={r.outputs[0]!} instance={k} inputs=[{detail}] bindings={changed}"
    journal s!"fired {← g.getTag} {label}"
    logInfo m!"CH-INSTANCE {← g.getTag} {label}"
    setGoals [← g.withContext do stamp g k]
    return (some k,none)
  catch err =>
    if err.isInterrupt || err.isRuntime then throw err
    saved.restore
    let why := firstLine (← err.toMessageData.toString)
    if let some entry := attempt then failedAttempts.modify (·.insert entry why)
    return (none,some why)

elab_rules : tactic
  | `(tactic| ch_on_fact $_h:ident of $_family:ident => $body:tactic) => withMainContext do
    let some p := body.raw.getPos? | throwError "missing producer location"
    let some e := body.raw.getTailPos? | throwError "missing producer end"
    let some idx := (← sites.get)[(p.byteIdx,e.byteIdx,body.raw.getKind)]? |
      throwError "ch_on_fact requires with_ch_root_catalog"
    let rule := (← registered.get)[idx]!
    let mut done := receipts (← getLCtx)
    for h in ← choices rule (← getLCtx) do
      let lookup := (← (← getMainGoal).getDecl).lctx.findFromUserName?
      let (key,_) ← tryInstance idx rule h done lookup
      if let some k := key then done := done.insert k

elab "drain_ch_witnesses" : tactic => withCurrHeartbeats do
  let rules ← registered.get
  if rules.isEmpty then throwError "empty witness catalog"
  let slow := (← IO.getEnv "CH_REPLAY_BASELINE").isSome
  let mut done := receipts (← (← getMainGoal).getDecl).lctx
  let mut fired := 0
  let mut passes := 0
  let mut go := true
  let mut failures := #[]
  let mut lookup := (← lookupFor slow (← (← getMainGoal).getDecl).lctx)
  let mut instancesSeen := 0
  let mut attempts := 0
  let mut attemptMs := 0
  let mut choiceMs := 0
  let mut viewMs := 0
  let mut instanceMs := 0
  let began ← IO.monoMsNow
  journal s!"start {← (← getMainGoal).getTag}"
  while go do
    go := false
    passes := passes+1
    failures := #[]
    let index := roleIndex (← (← getMainGoal).getDecl).lctx
    for idx in [:rules.size] do
      let r := rules[idx]!
      let c0 ← IO.monoMsNow
      let options ← choices r (← (← getMainGoal).getDecl).lctx
      choiceMs := choiceMs+((← IO.monoMsNow)-c0)
      if options.isEmpty then failures := failures.push s!"{r.outputs[0]!} | missing trigger"
      for anchor in options do
        let v0 ← IO.monoMsNow
        let candidates := views r (← inputRoles idx r) index
        viewMs := viewMs+((← IO.monoMsNow)-v0)
        for view in candidates do
          let began ← IO.monoMsNow
          let (key,why) ← tryInstance idx r anchor done lookup view
          instanceMs := instanceMs+((← IO.monoMsNow)-began)
          instancesSeen := instancesSeen+1
          if key.isSome || why.any (fun w=>!w.startsWith "missing ") then
            attempts := attempts+1
            attemptMs := attemptMs+((← IO.monoMsNow)-began)
            if (← IO.getEnv "CH_REPLAY_TIMING").isSome then
              logInfo m!"CH-LEGACY-TRY rule={idx}:{r.outputs[0]!} ms={(← IO.monoMsNow)-began} indexed={(← dependenciesOf r).isSome} result={why.getD "fired"}"
          if let some k := key then
            lookup := (← lookupFor slow (← (← getMainGoal).getDecl).lctx)
            done := done.insert k
            fired := fired+1
            go := true
          if let some why := why then failures := failures.push s!"{r.outputs[0]!} | {why}"
  let g ← getMainGoal
  logInfo m!"CH-CATALOG SUMMARY {← g.getTag}: producers={rules.size} added={fired} unavailable instances={failures.size} passes={passes} pending=0"
  journal s!"settled {← g.getTag} {passes} passes, {fired} added, {failures.size} unavailable"
  if (← IO.getEnv "CH_REPLAY_TIMING").isSome then
    logInfo m!"CH-LEGACY {← g.getTag} rules={rules.size} instances={instancesSeen} elaborated={attempts} added={fired} elaborationMs={attemptMs} triggerScanMs={choiceMs} viewMs={viewMs} instanceMs={instanceMs} totalMs={(← IO.monoMsNow)-began}"
  for f in failures do logInfo m!"CH-CATALOG waiting {f}"

private partial def resultHead : Expr → Name
  | .forallE _ _ b _ => resultHead b
  | .letE _ _ v b _ => resultHead (b.instantiate1 v)
  | .mdata _ b => resultHead b
  | e => e.getAppFn.constName?.getD .anonymous

/-- First-order matching on the expressions as written. Metavariable-headed
applications can accept terms of any shape. This keeps an unrelated row or
matrix expression from being evaluated during a speculative premise lookup. -/
private partial def sameShape (p a : Expr) : Bool := Id.run do
  if p == a || p.getAppFn.isMVar then return true
  match p,a with
  | .mdata _ b,_ => return sameShape b a
  | _,.mdata _ b => return sameShape p b
  | .forallE _ x y _,.forallE _ u v _
  | .lam _ x y _,.lam _ u v _ => return sameShape x u && sameShape y v
  | .app h x,.app k y => return sameShape h k && sameShape x y
  | .const n _,.const m _ => return n == m
  | .proj n i x,.proj m j y => return n == m && i == j && sameShape x y
  | _,_ => return false

private def exitRoutes (goal : Expr) : MetaM (Array (List Bool × Name)) := do
  let mut todo := [(goal, ([] : List Bool))]
  let mut result := #[]
  while let (e,route)::rest := todo do
    todo := rest
    let head := e.getAppFn.constName?.getD .anonymous
    if head != .anonymous && head != ``Or && head != ``Exists then
      result := result.push (route.reverse,head)
    let v ← whnf e
    if v.isAppOfArity ``Or 2 then
      let args := v.getAppArgs
      todo := (args[0]!,false::route)::(args[1]!,true::route)::todo
  return result

/-- Enumerate imported project theorems and live local suppliers whose conclusion
is one of the exit predicates. Commit only when every premise is discharged. -/
elab "check_ch_exits" literal:ident : tactic => withMainContext <| withCurrHeartbeats do
  let g ← getMainGoal
  let traceFile ← (← IO.getEnv "CH_CATALOG_TRACE_FILE").mapM fun path => IO.FS.Handle.mk path .append
  let traceLine := fun (line : String) => traceFile.forM fun file => file.putStrLn line
  traceLine s!"checking exits {← g.getTag}"
  let routes ← exitRoutes (← g.getType)
  let mut requests := routes.map fun (route,head)=>(route,head,(none : Option Expr))
  let deniedId ← getFVarId literal
  let locals ← ((← getLCtx).decls.toArray.filterMap id).mapM fun l => do
    return l.setType (← instantiateMVars l.type).consumeMData
  -- Keep the original order within each bucket, including same-named proofs.
  let mut localsByHead : Std.HashMap Name (Array LocalDecl) := {}
  for l in locals do
    unless l.isImplementationDetail do
      let h := resultHead l.type
      localsByHead := localsByHead.insert h ((localsByHead.getD h #[]).push l)
  -- A positive supplier for any live, explicitly rejected gate is also a proof
  -- of this goal. Include the literal CH target among those gates.
  let guards := (← guardNames.get).push `hnoCycle
  let mut literalSeen := false
  for l in locals do
    if l.fvarId == deniedId || guards.contains l.userName.eraseMacroScopes then
      if let some pos ← withReducible (matchNot? l.type) then
        let ty := (← instantiateMVars pos).consumeMData
        let head := ty.getAppFn.constName?.getD .anonymous
        if head != .anonymous && ![``And,``Or,``Exists,``Eq,``LE.le,``LT.lt,``Not].contains head then
          requests := requests.push ([],head,some l.toExpr)
          if l.fvarId == deniedId then
            traceLine s!"literal target {head}"
            literalSeen := true
  unless literalSeen do throwError "could not recover the literal positive target from {literal}"
  let heads := requests.map (fun x=>x.2.1)
  let env ← getEnv
  let lib := env.constants.fold (init := #[]) fun acc n ci =>
    if let .thmInfo th := ci then
      if (`LeanCH).isPrefixOf n || (`CH).isPrefixOf n then
        let h := resultHead th.type
        if heads.contains h then acc.push (h,n) else acc
      else acc
    else acc
  let mut count : Nat := 0
  for (route,head,denial) in requests do
    let mut candidates := #[]
    for (h,n) in lib do
      if h==head then candidates := candidates.push (n,← mkConstWithFreshMVarLevels n)
    for l in localsByHead.getD head #[] do
      candidates := candidates.push (l.userName,l.toExpr)
    for (name,e) in candidates do
      traceLine s!"exit {count+1} {head} {name}"
      count := count+1
      let saved ← Tactic.saveState
      let mut message := ""
      try
        let mut target := g
        if let some rejected := denial then
          let [neg] ← target.applyConst ``False.elim | throwError "cannot introduce contradiction"
          let [positive] ← neg.apply rejected | throwError "cannot open rejected gate"
          target := positive
        for right in route do
          let [child] ← target.applyConst (if right then ``Or.inr else ``Or.inl)
            | throwError "not a binary exit"
          target := child
        let goals ← withReducible (target.apply e)
        -- Discharge proof arguments before choosing any unforced data witness.
        let mut changed := true
        while changed do
          changed := false
          for m in goals do
            unless ← m.isAssigned do
              let ty ← instantiateMVars (← m.getType)
              if ← isProp ty then
                let h := resultHead ty
                for l in localsByHead.getD h #[] do
                  if sameShape ty l.type then
                    if ← withReducible (isDefEqGuarded l.type ty) then
                      m.assign l.toExpr
                      changed := true
                      break
        let remaining ← goals.filterM fun m=>return !(← m.isAssigned)
        if remaining.isEmpty then
          logInfo m!"CH-EXIT closed {head} with {name}"
          replaceMainGoal []
          return
        let mut labels := #[]
        for m in remaining do
          let d ← m.getDecl
          let ty ← instantiateMVars d.type
          labels := labels.push s!"{d.userName}:{resultHead ty}"
        message := String.intercalate ", " labels.toList
      catch err =>
        if err.isInterrupt || err.isRuntime then throw err
        message := "the conclusion did not apply to this goal with these parameters"
      saved.restore
      logInfo m!"CH-EXIT {head} via {name} | {message}"
    traceLine s!"tested {head}: {candidates.size} suppliers"
    traceFile.forM fun file => file.flush
  logInfo m!"CH-EXIT SUMMARY {← g.getTag} tested={count} direct predicate suppliers; no complete application"
end LeanCH.BR.CHContextCatalog
