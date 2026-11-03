import Blotto.GeneralPaperCompleteStoredPipelineWork
import Blotto.GeneralPaperStoredFramedWork

/-! Complete preparation after a successful accuracy parse. The exact
word-input work equals this continuation plus the accuracy preparation it
omits. Subtracting that actual omitted pass gives a complete price, with
uniform paper-input coefficients, for the same returned installed sampler. -/
namespace Blotto.GeneralPaperCompleteParsedPreparationWork
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (input prepare width)
open GeneralPaperEqualInputDomain (word)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem work_identity {n : ℕ} (model : RationalCostModel) (A K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).2 +
      (GeneralPaperBinaryAccuracy.prepare id A parsed.words).2 =
      (GeneralPaperStoredSelectedPipeline.run model A K (input model values v hv budget parsed)).2 := by
  rw [GeneralPaperStoredFramedWork.construction_work,
    GeneralPaperCompleteStoredPipelineWork.work_identity]
  have hSource := GeneralPaperStoredFramedWork.prepared_price_identity model A K values v hv budget parsed
  have hConstruction := congrArg
    (fun a => (GeneralPaperStoredSelectedConstruction.run model
      (word K (input model values v hv budget parsed)) a).2)
    (GeneralPaperStoredParsedPreparation.prepared_data model A K values v hv budget parsed)
  have hWidth := congrArg (fun a => a.address)
    (GeneralPaperStoredParsedPreparation.prepared_data model A K values v hv budget parsed)
  simp only [width]
  rw [hConstruction,hWidth]
  dsimp only [input] at *
  omega

def price {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) : ℕ :=
  let p := input model values v hv budget parsed
  GeneralPaperCompleteStoredPipelineWork.price model K p -
    (GeneralPaperBinaryAccuracy.prepare id (word K p) parsed.words).2

theorem work {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    (GeneralPaperStoredParsedPreparation.run model (word K (input model values v hv budget parsed))
      K values v hv budget parsed).2 ≤ price model K values v hv budget parsed := by
  have hJoin := work_identity model (word K (input model values v hv budget parsed)) K values v hv budget parsed
  have hFull := GeneralPaperCompleteStoredPipelineWork.work model K (input model values v hv budget parsed)
  dsimp only [price]
  omega

theorem price_le {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    price model K values v hv budget parsed ≤
      GeneralPaperCompleteStoredPipelineWork.price model K (input model values v hv budget parsed) :=
  Nat.sub_le _ _

theorem returned_work {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed)
    (returned : Installed (width model (word K (input model values v hv budget parsed)) K values v hv budget parsed))
    (hReturn : (GeneralPaperStoredParsedPreparation.run model (word K (input model values v hv budget parsed))
      K values v hv budget parsed).1 = some returned) :
    returned.work ≤ price model K values v hv budget parsed := by
  rw [(GeneralPaperStoredParsedPreparation.every_returned model _ K values v hv budget parsed returned hReturn).1]
  exact work model K values v hv budget parsed

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ,∀ (n : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed),
      (GeneralPaperStoredParsedPreparation.run model (word K (input model values v hv budget parsed))
        K values v hv budget parsed).2 ≤
        C * GeneralPaperEqualInputHeadline.inputSize (input model values v hv budget parsed) *
          (GeneralPaperEqualInputHeadline.paperLog (input model values v hv budget parsed)) ^ d := by
  obtain ⟨C,d,hPrice⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K)
  exact ⟨C,d,fun _ values v hv budget parsed =>
    (work model K values v hv budget parsed).trans
      ((price_le model K values v hv budget parsed).trans (hPrice _))⟩

theorem epsilon_constructed {n : ℕ} (model : RationalCostModel) (K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (hBudget : 0 < budget) (parsed : Parsed)
    (hOne : GeneralPaperEqualInputHeadline.epsilon (input model values v hv budget parsed) < 1) :
    let A := word K (input model values v hv budget parsed)
    ∃ returned : Installed (width model A K values v hv budget parsed),
      (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some returned ∧
      returned.work = (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).2 ∧
      returned.work ≤ price model K values v hv budget parsed ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model (width model A K values v hv budget parsed)
        returned (prepare model A K values v hv budget parsed).1.branch
      Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤
        (GeneralPaperEqualInputHeadline.epsilon (input model values v hv budget parsed) : ℝ) := by
  dsimp only
  obtain ⟨returned,hReturn,hWork,_⟩ := GeneralPaperStoredParsedPreparation.source model
    (word K (input model values v hv budget parsed)) K values v hv budget parsed
  exact ⟨returned,hReturn,hWork,returned_work model K values v hv budget parsed returned hReturn,
    GeneralPaperStoredParsedPreparation.epsilon model _ K values v hv budget hBudget parsed hOne returned hReturn⟩

end Blotto.GeneralPaperCompleteParsedPreparationWork
