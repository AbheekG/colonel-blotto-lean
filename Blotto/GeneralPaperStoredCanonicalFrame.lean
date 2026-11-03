import Blotto.GeneralPaperStoredFramedContract

/-! Every positive rational accuracy has a successful canonical frame.
The exact parsed exponent drives the stored construction once; the same
actual returned memory has the original epsilon-Nash law and full price. -/
namespace Blotto.GeneralPaperStoredCanonicalFrame
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (width prepare)
open GeneralPaperStoredFramedPreparation (Output finish run)
open GeneralPaperStoredFramedContract (epsilon)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

theorem every_returned {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (frame : List Bool) (returned : Output) (hReturn : (run model A K values v hv budget frame).1 = some returned) :
    ∃ (parsed : Parsed) (suffix : List Bool),
      (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix) ∧
      returned.2.2 = suffix ∧ returned.2.1.work = (run model A K values v hv budget frame).2 ∧
      GeneralPaperStoredSelectedDraw.Refines model returned.1 returned.2.1 (prepare model A K values v hv budget parsed).1.branch ∧
      (0 < budget → epsilon parsed < 1 →
        let μ := GeneralPaperStoredSelectedLaw.outputLaw model returned.1 returned.2.1 (prepare model A K values v hv budget parsed).1.branch
        Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (epsilon parsed : ℝ)) := by
  obtain ⟨parsed,suffix,inner,hRead,hBuild,hEq,hWork⟩ := GeneralPaperStoredFramedPreparation.every_returned model A K values v hv budget frame returned hReturn
  subst returned
  exact ⟨parsed,suffix,hRead,rfl,hWork,
    GeneralPaperStoredFramedPreparation.finished_refines model A K values v hv budget parsed inner hBuild _ suffix,
    fun hBudget hOne => GeneralPaperStoredFramedContract.equilibrium model A K values v hv budget hBudget parsed hOne inner hBuild _ suffix⟩

theorem epsilon_constructed {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (hBudget : 0 < budget)
    (eps : ℚ) (hPositive : 0 < eps) (hOne : eps < 1) (suffix : List Bool) :
    let frame := BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive) ++ suffix
    ∃ (parsed : Parsed) (returned : Output),
      (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix) ∧ epsilon parsed = eps ∧
      parsed.exponent = (GeneralPaperDyadicAccuracy.prepare eps).exponent ∧
      (run model A K values v hv budget frame).1 = some returned ∧ returned.2.2 = suffix ∧
      returned.2.1.work = (run model A K values v hv budget frame).2 ∧
      GeneralPaperStoredSelectedDraw.Refines model returned.1 returned.2.1 (prepare model A K values v hv budget parsed).1.branch ∧
      let μ := GeneralPaperStoredSelectedLaw.outputLaw model returned.1 returned.2.1 (prepare model A K values v hv budget parsed).1.branch
      Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  let frame := BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive) ++ suffix
  obtain ⟨parsed,inner,hRead,hNumeric,hBuild,hRun,hWork⟩ := GeneralPaperStoredFramedPreparation.complete model A K values v hv budget
    (GeneralPaperBinaryAccuracy.input eps hPositive) suffix
  have hEps : epsilon parsed = eps :=
    (GeneralPaperStoredFramedContract.epsilon_numeric parsed _ hNumeric).trans (GeneralPaperBinaryAccuracy.input_value eps hPositive)
  have hExponent := GeneralPaperBinaryAccuracy.read_exponent id A frame (parsed,suffix) hRead eps hEps.symm
  let returned := finish A (GeneralPaperBinaryAccuracy.read id A frame).2 inner suffix
  refine ⟨parsed,returned,hRead,hEps,hExponent,hRun,rfl,hWork,
    GeneralPaperStoredFramedPreparation.finished_refines model A K values v hv budget parsed inner hBuild _ suffix,?_⟩
  have hEquilibrium := GeneralPaperStoredFramedContract.equilibrium model A K values v hv budget hBudget parsed
    (by rw [hEps]; exact hOne) inner hBuild (GeneralPaperBinaryAccuracy.read id A frame).2 suffix
  simpa only [hEps,returned,finish] using hEquilibrium

theorem canonical_length (eps : ℚ) (hPositive : 0 < eps) :
    (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive)).length = 2 * rationalWordWidth eps :=
  GeneralPaperBinaryAccuracy.input_length eps hPositive

end Blotto.GeneralPaperStoredCanonicalFrame
