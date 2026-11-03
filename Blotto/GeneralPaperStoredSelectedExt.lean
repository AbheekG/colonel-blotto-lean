import Blotto.GeneralPaperStoredSelectedLaw

/-! Construction-work metadata does not affect actual draw execution.
Equal memory and root preserve the complete result, including state, reads
and work; this permits one preparation-price attachment without rebuilding. -/
namespace Blotto.GeneralPaperStoredSelectedExt
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

theorem run_ext {S : Type*} (model : RationalCostModel) (A : ℕ) (first second : Installed A)
    (hMemory : first.memory = second.memory) (hRoot : first.root = second.root) (cap : ℕ)
    (tape : ℕ → List Bool) (next : S → Bool × S) (state : S) :
    GeneralPaperStoredSelectedDraw.run model A first cap tape next state =
      GeneralPaperStoredSelectedDraw.run model A second cap tape next state := by
  rcases first with ⟨memory,root,work⟩
  rcases second with ⟨otherMemory,otherRoot,otherWork⟩
  dsimp only at hMemory hRoot
  subst otherMemory
  subst otherRoot
  rfl

theorem refines_ext {n : ℕ} (model : RationalCostModel) (A : ℕ) (first second : Installed A)
    (hMemory : first.memory = second.memory) (hRoot : first.root = second.root)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : GeneralPaperEqualBitBranch.Prepared v k budget)
    (hRefines : GeneralPaperStoredSelectedDraw.Refines model A first p) :
    GeneralPaperStoredSelectedDraw.Refines model A second p := by
  cases p with
  | dominant chosen heavy row correct =>
    intro cap tape fresh
    rw [← run_ext model A first second hMemory hRoot cap tape GeneralPaperBooleanFreshWord.nextList fresh]
    exact hRefines cap tape fresh
  | grouped small sampler hK hB =>
    intro cap tape fresh
    rw [← run_ext model A first second hMemory hRoot cap
      (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)]
    exact hRefines cap tape fresh

theorem attach {n : ℕ} (model : RationalCostModel) (S A prefixWork : ℕ) (first : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : GeneralPaperEqualBitBranch.Prepared v k budget)
    (hRefines : GeneralPaperStoredSelectedDraw.Refines model A first p) :
    GeneralPaperStoredSelectedDraw.Refines model A (GeneralPaperSamplerRecordInstallation.attach S A prefixWork first) p :=
  refines_ext model A first _ rfl rfl p hRefines

end Blotto.GeneralPaperStoredSelectedExt
