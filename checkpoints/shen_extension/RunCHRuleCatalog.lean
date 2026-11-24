import checkpoints.shen_extension.CHRuleCatalog

open LeanCH.BR.CHRuleCatalog

/-- With no indices, select the whole local catalog. Pass --checks to include skipped attempts. -/
def main (args : List String) : IO UInt32 := do
  let indexed := rules.zipIdx
  if args.contains "--list" then
    for (r,i) in indexed do
      IO.println s!"{i}  {repr (r.source::r.extra)} -> {repr r.target}  [{r.name}]"
    return 0
  let guardName := fun (g : LeanCH.BR.CHRootExclusions.Gate) => ((reprStr g).splitOn ".").getLast!
  let guards := LeanCH.BR.CHRootExclusions.gates
  if args.contains "--audit-guards" then
    for g in guards do
      let r := runFrom rules [.counterexample,.guard g]
      IO.println s!"{guardName g}  settled={r.closed rules}  contradiction={r.seen.contains .contradiction}"
      unless r.closed rules && r.seen.contains .contradiction do return 1
    return 0
  let requested := (args.filter (·.startsWith "--guard=")).map (fun a => (a.drop 8).toString)
  if requested.any (fun s => !guards.any (fun g => guardName g==s)) then
    IO.eprintln "Unknown guard. --audit-guards lists the supported names."
    return 2
  let indices := args.filter (fun a=>a != "--checks" && a != "--shen-window" && !a.startsWith "--guard=")
  if indices.any (fun s=>!(s.toNat?.any (· < rules.length))) then
    IO.eprintln "Select rule numbers from --list, or omit numbers to run the entire catalog."
    return 2
  let selected := (indexed.filter fun (_,i)=>indices.isEmpty || indices.contains (toString i)).map Prod.fst
  let base : List Family := if args.contains "--shen-window" then [.counterexample,.shenWindow] else [.counterexample]
  let seeds := base ++ (guards.filter (fun g => requested.contains (guardName g))).map Family.guard
  let result := runFrom selected seeds
  IO.println s!"start {repr seeds}; {selected.length} selected entries"
  for e in result.log.reverse do
    if args.contains "--checks" || e.outcome != "premise absent or other input family" then
      IO.println s!"{repr e.atFamily} | {e.rule} | {e.outcome} | {repr e.target}"
  IO.println s!"families={result.seen.length}  tested={result.log.length}  pending={result.pending.length}  closed_under_selection={result.closed selected}  contradiction={result.seen.contains .contradiction}"
  return if result.closed selected then 0 else 1
