import Blotto.GeneralPaperOriginalGameInput

/-! One original-input branch dispatcher. The one-field case precedes all
accuracy/source preparation. Unequal preparation uses the existing native
analysis calibration; erasure of that analysis from executable data remains
a separate implementation join. -/
namespace Blotto.GeneralPaperAllBranchBitDispatch
open GeneralPaperOriginalGameInput
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

inductive Prepared (n : ℕ)
  | oneField (h : n = 1) (rich poor : RationalResourceArray 1)
  | equal (A : ℕ) (output : Installed A)
  | unequal (output : GeneralPaperClosedStrategyDriver.Prepared n)

def one (p : Input) (h : p.n = 1) : Prepared p.n × ℕ :=
  let actual := GeneralPaperOneFieldRealPreparation.run 1 p.budget
  (.oneField h actual.1.1 actual.1.2,actual.2 * (rationalWordWidth p.budget + 3) + 64)

def equal (model : RationalCostModel) (K : ℕ) (p : Input) : Option (Prepared p.n) × ℕ :=
  let input := equalInput model p
  let W := GeneralPaperEqualInputDomain.word K input
  let actual := GeneralPaperStoredSelectedPipeline.run model W K input
  (actual.1.map (Prepared.equal (GeneralPaperStoredSelectedPipeline.width model W K input)),actual.2)

noncomputable def unequal (model : RationalCostModel) (C d : ℕ) (p : Input) (h : p.budget < 1) : Prepared p.n × ℕ :=
  let input := unequalInput p h
  let W := GeneralPaperNativeResourceReferenceGrowth.word model C d input
  let actual := GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget ⟨p.budget_valid.1,h⟩
  (.unequal actual.1,actual.2)

def branchPrice (model : RationalCostModel) (p : Input) : ℕ :=
  model.rat (rationalWordWidth p.budget + 3) + 64 * (binaryWordWidth p.n + 1)

noncomputable def run (model : RationalCostModel) (C d K : ℕ) (p : Input) : Option (Prepared p.n) × ℕ :=
  if hN : p.n = 1 then
    let actual := one p hN
    (some actual.1,actual.2 + 64 * (binaryWordWidth p.n + 1))
  else if hB : p.budget = 1 then
    let actual := equal model K p
    (actual.1,actual.2 + branchPrice model p)
  else
    let actual := unequal model C d p (strict_of_ne p hB)
    (some actual.1,actual.2 + branchPrice model p)

theorem on_one (model : RationalCostModel) (C d K : ℕ) (p : Input) (hN : p.n = 1) :
    run model C d K p = (some (one p hN).1,(one p hN).2 + 64 * (binaryWordWidth p.n + 1)) := by
  simp [run,hN]

theorem on_equal (model : RationalCostModel) (C d K : ℕ) (p : Input) (hN : p.n ≠ 1) (hB : p.budget = 1) :
    run model C d K p = ((equal model K p).1,(equal model K p).2 + branchPrice model p) := by
  simp [run,hN,hB]

theorem on_unequal (model : RationalCostModel) (C d K : ℕ) (p : Input) (hN : p.n ≠ 1) (hB : p.budget ≠ 1) :
    run model C d K p = (some (unequal model C d p (strict_of_ne p hB)).1,
      (unequal model C d p (strict_of_ne p hB)).2 + branchPrice model p) := by
  simp [run,hN,hB]

end Blotto.GeneralPaperAllBranchBitDispatch
