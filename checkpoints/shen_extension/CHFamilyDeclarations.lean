import Lean

namespace LeanCH.BR.CHFamilyWorklist
open Lean Meta Elab Command Tactic

structure Branch (P : Prop) : Prop where
  evidence : P

initialize splitRules : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun a n => if a.contains n then a else a.push n
    addImportedFn := fun modules => Id.run do
      let mut names := #[]
      for entries in modules do
        for n in entries do
          unless names.contains n do names := names.push n
      return names
  }

/-- Declare the result pattern of a theorem as a family split. Raw evidence
of that pattern may arrive before replay or through either producer engine. -/
elab "ch_family_split_result " th:ident : command => do
  let n ← resolveGlobalConstNoOverload th
  modifyEnv (splitRules.addEntry · n)

initialize splitPredicates : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun modules => Id.run do
      let mut names : NameSet := {}
      for entries in modules do
        for n in entries do names := names.insert n
      return names
  }

/-- A named family whose definition gives its exhaustive alternatives. -/
elab "ch_family_split_predicate " pred:ident : command => do
  let n ← resolveGlobalConstNoOverload pred
  modifyEnv (splitPredicates.addEntry · n)

/-- An explicit designation for a particular proof, including an abstract
P ∨ Q whose shape alone cannot distinguish it from an ordinary disjunction. -/
elab "ch_family_split " h:term : tactic => withMainContext do
  let proof ← elabTerm h none
  let marked ← mkAppM ``Branch.mk #[proof]
  let (_,next) ← (← getMainGoal).note (← mkFreshUserName `chSplit) marked
  replaceMainGoal [next]

end LeanCH.BR.CHFamilyWorklist
