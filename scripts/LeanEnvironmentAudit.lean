import Blotto
import Lean

/-! Verification tooling, outside the mathematical library. Inspect the actual
compiled environment, including private helpers, projections and generated
declarations that a source-text declaration scanner cannot enumerate. -/
open Lean in
run_meta do
  let env ← getEnv
  let importedProjectModules := env.header.moduleNames.filter fun mod =>
    (`Blotto).isPrefixOf mod && mod != `Blotto
  let mut count := 0
  let mut privateCount := 0
  let mut theoremCount := 0
  let mut modules : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  let mut names : Array String := #[]
  let mut compilerHelpers : Array String := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Blotto).isPrefixOf mod do continue
    count := count + 1
    names := names.push name.toString
    modules := modules.insert mod
    if isPrivateName name then privateCount := privateCount + 1
    if ci matches .thmInfo _ then theoremCount := theoremCount + 1
    if ci.isUnsafe || ci.isPartial then
      -- Lean generates this optimized implementation for well-founded
      -- recursion. It is not available to safe logical declarations. Do not
      -- confuse its executable code with an axiom or a kernel-checked proof.
      unless name.toString.endsWith "._unsafe_rec" do
        throwError "unexpected unsafe project declaration: {name}"
      compilerHelpers := compilerHelpers.push name.toString
      continue
    if ci matches .axiomInfo _ then
      throwError "project axiom: {name}"
    for ax in ← collectAxioms name do
      unless #[`Classical.choice, `Quot.sound, `propext].contains ax do
        throwError "unapproved axiom {ax} in {name}"
      axioms := axioms.insert ax
  let result := Json.mkObj [
    ("declarations", toJson count), ("private_declarations", toJson privateCount),
    ("theorems", toJson theoremCount), ("modules", toJson importedProjectModules.size),
    ("modules_with_declarations", toJson modules.size),
    ("axioms", toJson (axioms.toList.map Name.toString)), ("names", toJson names),
    ("compiler_unsafe_rec_helpers", toJson compilerHelpers)]
  logInfo m!"ENVIRONMENT_AUDIT {result.compress}"
