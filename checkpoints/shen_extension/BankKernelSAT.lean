import Lean.Meta.Tactic.BVDecide.LRAT.Cert
import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Elab.Tactic

/-! A propositional SAT certificate is expanded into resolution inferences
checked by the kernel. The external solver only supplies the proof trace. -/
namespace LeanCH.BR.TripleBank.KernelSAT

private theorem andL (a b : Prop) : ¬ ((a ∧ b) ∧ ¬a) := fun h => h.2 h.1.1
private theorem andR (a b : Prop) : ¬ ((a ∧ b) ∧ ¬b) := fun h => h.2 h.1.2
private theorem andI (a b : Prop) : ¬ (¬(a ∧ b) ∧ a ∧ b) := fun h => h.1 h.2
private theorem orL (a b : Prop) : ¬ (¬(a ∨ b) ∧ a) := fun h => h.1 (Or.inl h.2)
private theorem orR (a b : Prop) : ¬ (¬(a ∨ b) ∧ b) := fun h => h.1 (Or.inr h.2)
private theorem orE (a b : Prop) : ¬ ((a ∨ b) ∧ ¬a ∧ ¬b) := fun h => h.1.elim h.2.1 h.2.2
private theorem impL (a b : Prop) : ¬ (¬(a → b) ∧ ¬a) := fun h => h.1 (fun ha => (h.2 ha).elim)
private theorem impR (a b : Prop) : ¬ (¬(a → b) ∧ b) := fun h => h.1 (fun _ => h.2)
private theorem impE (a b : Prop) : ¬ ((a → b) ∧ a ∧ ¬b) := fun h => h.2.2 (h.1 h.2.1)
private theorem notL (a : Prop) : ¬ ((¬a) ∧ a) := fun h => h.1 h.2
private theorem notR (a : Prop) : ¬ (¬(¬a) ∧ ¬a) := fun h => h.1 h.2
private theorem asserted (a : Prop) (h : a) : ¬ ¬a := fun no => no h

open Lean Meta Elab Tactic
open Lean.Meta.Tactic.BVDecide
open Std.Tactic.BVDecide

private structure Table where
  vars : Array Expr := #[]
  ids : Std.HashMap Expr Int := {}
  atoms : Array (Expr × Int) := #[]
  clauses : Array (Array Int) := #[]
  rejects : Array Expr := #[]

private abbrev Build := StateRefT Table MetaM

private def clause (xs : Array Int) (proof : Expr) : Build Unit :=
  modify fun s => {s with clauses := s.clauses.push xs, rejects := s.rejects.push proof}

private partial def intern (p : Expr) : Build Int := do
  let p := p.consumeMData.headBeta
  if let some i := (← get).ids[p]? then return i
  let atom := !(p.isAppOfArity ``Not 1 || p.isAppOfArity ``And 2 || p.isAppOfArity ``Or 2 ||
    p.isForall || p.isConstOf ``True || p.isConstOf ``False)
  if atom then
    unless p.isAppOfArity ``Eq 3 do
      let q ← whnf p
      if q != p then
        let j ← intern q
        modify fun s => {s with ids := s.ids.insert p j}
        return j
    for (a,j) in (← get).atoms do
      if ← isDefEq p a then
        modify fun s => {s with ids := s.ids.insert p j}
        return j
  let i : Int := Int.ofNat ((← get).vars.size+1)
  modify fun s => {s with vars := s.vars.push p, ids := s.ids.insert p i}
  if atom then modify fun s => {s with atoms := s.atoms.push (p,i)}
  if p.isAppOfArity ``Not 1 then
    let a := p.appArg!
    let j ← intern a
    clause #[-i,-j] (mkApp (mkConst ``notL) a)
    clause #[i,j] (mkApp (mkConst ``notR) a)
  else if p.isAppOfArity ``And 2 then
    let a := p.appFn!.appArg!
    let b := p.appArg!
    let j ← intern a
    let k ← intern b
    clause #[-i,j] (mkApp2 (mkConst ``andL) a b)
    clause #[-i,k] (mkApp2 (mkConst ``andR) a b)
    clause #[i,-j,-k] (mkApp2 (mkConst ``andI) a b)
  else if p.isAppOfArity ``Or 2 then
    let a := p.appFn!.appArg!
    let b := p.appArg!
    let j ← intern a
    let k ← intern b
    clause #[i,-j] (mkApp2 (mkConst ``orL) a b)
    clause #[i,-k] (mkApp2 (mkConst ``orR) a b)
    clause #[-i,j,k] (mkApp2 (mkConst ``orE) a b)
  else if let .forallE _ a b _ := p then
    unless b.hasLooseBVars do
      let j ← intern a
      let k ← intern b
      clause #[i,j] (mkApp2 (mkConst ``impL) a b)
      clause #[i,-k] (mkApp2 (mkConst ``impR) a b)
      clause #[-i,-j,k] (mkApp2 (mkConst ``impE) a b)
  else if p.isConstOf ``True then
    clause #[i] (mkApp2 (mkConst ``asserted) p (mkConst ``True.intro))
  else if p.isConstOf ``False then
    clause #[-i] (mkApp (mkConst ``id [.zero]) p)
  return i

private partial def antecedents (p : Expr) (acc : Array Expr := #[]) : Array Expr × Expr :=
  let p := p.consumeMData.headBeta
  if p.isAppOfArity ``Not 1 then (acc.push p.appArg!, mkConst ``False)
  else match p with
  | .forallE _ a b _ => if b.hasLooseBVars then (acc,p) else antecedents b (acc.push a)
  | _ => (acc,p)

private partial def assumeTrue (p h : Expr) : Build Unit := do
  if p.isAppOfArity ``And 2 then
    let a := p.appFn!.appArg!
    let b := p.appArg!
    assumeTrue a (mkApp3 (mkConst ``And.left) a b h)
    assumeTrue b (mkApp3 (mkConst ``And.right) a b h)
  else
    let (args,result) := antecedents p
    if args.isEmpty then
      let i ← intern p
      clause #[i] (mkApp2 (mkConst ``asserted) p h)
    else
      let mut literals := #[]
      for a in args do literals := literals.push (-(← intern a))
      let mut types := args
      unless result.isConstOf ``False do
        literals := literals.push (← intern result)
        types := types.push (mkNot result)
      let tree := types.toList.reverse.tail!.foldl (fun t a => mkAnd a t) types.back!
      let proof ← withLocalDeclD `bad tree fun bad => do
        let mut cur := bad
        let mut type := tree
        let mut old := h
        for i in [:args.size] do
          if i+1 = types.size then old := mkApp old cur
          else
            let a := type.appFn!.appArg!
            let b := type.appArg!
            old := mkApp old (mkApp3 (mkConst ``And.left) a b cur)
            cur := mkApp3 (mkConst ``And.right) a b cur
            type := b
        mkLambdaFVars #[bad] (if result.isConstOf ``False then old else mkApp cur old)
      clause literals proof

private def falsified (vars : Array Expr) (i : Int) : Expr :=
  let a := vars[i.natAbs-1]!
  if i < 0 then a else mkNot a

private abbrev Database := Std.HashMap Nat (Array Int × Expr)

private def curryClause (vars : Array Expr) (ls : Array Int) (reject : Expr) : MetaM Expr := do
  let types := ls.map (falsified vars)
  withLocalDeclsDND (types.map fun p => (`h,p)) fun xs => do
    let mut pair := xs.back!
    let mut ty := types.back!
    for j in [:xs.size-1] do
      let i := xs.size-2-j
      pair := mkApp4 (mkConst ``And.intro) types[i]! ty xs[i]! pair
      ty := mkAnd types[i]! ty
    mkLambdaFVars xs (mkApp reject pair)

/-- Replay one reverse-unit-propagation inference as ordinary implication
elimination. Every assigned literal is an actual Lean proof. -/
private def derive (vars : Array Expr) (db : Database) (ls : Array Int) (hints : Array Nat) :
    MetaM Expr := do
  withLocalDeclsDND (ls.map fun l => (`h,falsified vars l)) fun assumptions => do
    let mut facts : Std.HashMap Int Expr := {}
    for i in [:ls.size] do facts := facts.insert ls[i]! assumptions[i]!
    let mut lctx ← getLCtx
    let mut lets := #[]
    for id in hints do
      let some (cl,proof) := db[id]? | throwError "unknown LRAT clause {id}"
      let unassigned := cl.filter fun l => !facts.contains l
      if unassigned.isEmpty then
        let contradiction := mkAppN proof (cl.map fun l => facts[l]!)
        let result ← withLCtx' lctx <| mkLetFVars lets contradiction
        return ← mkLambdaFVars assumptions result
      unless unassigned.size = 1 do throwError "invalid unit propagation at clause {id}"
      let pivot := unassigned[0]!
      let unitProof ← withLCtx' lctx <| withLocalDeclD `unit (falsified vars pivot) fun unit => do
        let pr := mkAppN proof (cl.map fun l => if l == pivot then unit else facts[l]!)
        let nn ← mkLambdaFVars #[unit] pr
        return if pivot < 0 then nn else mkApp2 (mkConst ``Classical.byContradiction) (falsified vars (-pivot)) nn
      let fvar ← mkFreshFVarId
      lctx := lctx.mkLetDecl fvar `unit (falsified vars (-pivot)) unitProof
      facts := facts.insert (-pivot) (mkFVar fvar)
      lets := lets.push (mkFVar fvar)
    throwError "LRAT clause did not end in a conflict"

private def clauseType (vars : Array Expr) (ls : Array Int) :=
  ls.foldr (fun i b => mkForall `h .default (falsified vars i) b) (mkConst ``False)

private partial def bundle (types proofs : Array Expr) (lo hi : Nat) : Expr × Expr :=
  if hi = lo+1 then (types[lo]!, proofs[lo]!)
  else
    let mid := (lo+hi)/2
    let (a,ha) := bundle types proofs lo mid
    let (b,hb) := bundle types proofs mid hi
    (mkAnd a b, mkApp4 (mkConst ``And.intro) a b ha hb)

private inductive Premises where
  | leaf (index : Nat) (type : Expr)
  | pair (type : Expr) (left right : Premises)
deriving Inhabited

private def Premises.typeOf : Premises → Expr
  | .leaf _ type | .pair type _ _ => type

/-- Name the branches of the premise tree. This keeps each projection
logarithmic in the number of input clauses. -/
private partial def premiseTree (types : Array Expr) (v : Expr) (lo hi : Nat) : MetaM Premises := do
  if hi = lo+1 then return .leaf lo types[lo]!
  let mid := (lo+hi)/2
  let left ← premiseTree types v lo mid
  let right ← premiseTree types v mid hi
  let name ← mkAuxDeclName `bankPremises
  addDecl <| .defnDecl {
    name, levelParams := []
    type := ← mkForallFVars #[v] (mkSort .zero)
    value := ← mkLambdaFVars #[v] (mkAnd left.typeOf right.typeOf)
    hints := .abbrev
    safety := .safe }
  return .pair (mkApp (mkConst name) v) left right

private def unpack (s : Table) (tree : Premises) (h : Expr) (db : Database) : Database :=
  match tree with
  | .leaf i _ => db.insert (i+1) (s.clauses[i]!,h)
  | .pair _ left right =>
    let a := left.typeOf
    let b := right.typeOf
    unpack s right (mkApp3 (mkConst ``And.right) a b h)
      (unpack s left (mkApp3 (mkConst ``And.left) a b h) db)

private partial def lookupProp (xs : Array Expr) (n : Expr) (lo hi : Nat) : MetaM Expr := do
  if hi = lo+1 then return xs[lo]!
  let mid := (lo+hi)/2
  let test ← mkAppM ``LT.lt #[n,mkNatLit mid]
  mkAppM ``ite #[test, ←lookupProp xs n lo mid, ←lookupProp xs n mid hi]

/-- Abstract the arc propositions once. Learned clauses are separate lemmas
over a valuation, so their kernel proofs can be checked independently. -/
private def reconstruct (s : Table) (trace : Array LRAT.IntAction) : MetaM Expr := do
  let pred := mkArrow (mkConst ``Nat) (mkSort .zero)
  let unsat ← withLocalDeclD `v (←pred) fun v => do
    let vs := (Array.range s.vars.size).map fun i => mkApp v (mkNatLit i)
    let types := s.clauses.map (clauseType vs)
    let whole ← premiseTree types v 0 types.size
    trace[Meta.Tactic.sat] "Checking {trace.size} LRAT steps for {types.size} premise clauses."
    withLocalDeclD `h whole.typeOf fun h => do
      let mut db := unpack s whole h {}
      for action in trace do
        match action with
        | .del ids => db := ids.foldl (fun d i => d.erase i) db
        | .addRat .. => throwError "expected a reverse-unit-propagation certificate"
        | .addEmpty _ hints | .addRup _ #[] hints =>
          let pr ← derive vs db #[] hints
          let name ← mkAuxDeclName `bankConflict
          addDecl <| .thmDecl {
            name, levelParams := []
            type := ← mkForallFVars #[v,h] (mkConst ``False)
            value := ← mkLambdaFVars #[v,h] pr }
          return mkConst name
        | .addRup id ls hints =>
          let pr ← derive vs db ls hints
          let name ← mkAuxDeclName `bankResolution
          addDecl <| .thmDecl {
            name, levelParams := []
            type := ← mkForallFVars #[v,h] (clauseType vs ls)
            value := ← mkLambdaFVars #[v,h] pr }
          db := db.insert id (ls,mkApp2 (mkConst name) v h)
      throwError "certificate contains no final empty clause"
  let rho ← withLocalDeclD `i (mkConst ``Nat) fun n =>
    do mkLambdaFVars #[n] (← lookupProp s.vars n 0 s.vars.size)
  let mut ps := #[]
  for i in [:s.clauses.size] do ps := ps.push (← curryClause s.vars s.clauses[i]! s.rejects[i]!)
  let input := (bundle (s.clauses.map (clauseType s.vars)) ps 0 ps.size).2
  return mkApp2 unsat rho input

/-- Refute the propositional hypotheses by a kernel-checked LRAT proof. -/
elab "bank_kernel_sat" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  unless (← g.getType).isConstOf ``False do throwError "expected a contradiction goal"
  let main : Build Unit := do
    for l in (← getLCtx) do
      unless l.isImplementationDetail do
        if ← isProp l.type then assumeTrue l.type l.toExpr
  let (_, s) ← main.run {}
  let lines := s.clauses.map fun c => String.intercalate " " (c.toList.map toString) ++ " 0"
  let dimacs := s!"p cnf {s.vars.size} {s.clauses.size}\n" ++ String.intercalate "\n" lines.toList ++ "\n"
  let solver := (← IO.appDir) / (if System.Platform.isWindows then "cadical.exe" else "cadical")
  let lrat ← IO.FS.withTempFile fun input inputPath => do
    input.putStr dimacs
    input.flush
    IO.FS.withTempFile fun _ certPath => do
      let result ← External.satQuery solver inputPath certPath 120 false .proof
      match result with
      | .sat _ => throwError "propositional assumptions admit a model"
      | .unsat => LratCert.load certPath true
  trace[Meta.Tactic.sat] "Reconstructing the certificate for {s.vars.size} propositional variables."
  g.assign (← reconstruct s lrat)

end LeanCH.BR.TripleBank.KernelSAT
