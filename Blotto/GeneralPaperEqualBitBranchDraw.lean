import Blotto.GeneralPaperEqualBitAccuracyDispatch

/-! Actual branch-dependent bit observations. The pure branch copies its
stored row without random reads; the grouped branch uses its existing full
fair-bit controller. Whole trace products give independent player outputs. -/
namespace Blotto.GeneralPaperEqualBitBranchDraw
open MeasureTheory
open GeneralPaperEqualBitBranch (Prepared outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 2200000

def copyRow {n : ℕ} (A : ℕ) (row : RationalResourceArray n) : RationalResourceArray n × ℕ :=
  let actual := PaperIndexedArrayConstruction.run id A
    (fun j : Fin n => (row.allocation j, rationalWordWidth (row.allocation j) + 32 * A + 32))
  (⟨actual.1.data, actual.1.size⟩, actual.2 + 64 * A + 64)

theorem copy_data {n : ℕ} (A : ℕ) (row : RationalResourceArray n) :
    (copyRow A row).1.realAllocation = row.realAllocation := by
  funext j
  change (((PaperIndexedArrayConstruction.run id A
    (fun j : Fin n => (row.allocation j, rationalWordWidth (row.allocation j) + 32 * A + 32))).1.read j : ℚ) : ℝ) = _
  rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
  rfl

def Trace {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : Prepared v k budget → Type
  | .dominant _ _ _ _ => Unit
  | .grouped _ sampler _ _ => GeneralPaperEqualRejectionTraceMeasure.Trace sampler.prepared.D sampler.prepared.midpointBits

instance measurableTrace {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    MeasurableSpace (Trace p) := ⊤

noncomputable def unitLaw : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩

noncomputable def traceLaw {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    ProbabilityMeasure (Trace p) :=
  match p with
  | .dominant _ _ _ _ => unitLaw
  | .grouped _ sampler _ _ => GeneralPaperEqualRejectionTraceMeasure.law sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared)

noncomputable def observed {n : ℕ} (model : RationalCostModel) (A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) : Trace p → GeneralPaperEqualFullBitDraw.Result n :=
  match p with
  | .dominant _ _ row _ => fun _ => let copied := copyRow A row; ⟨some copied.1, 0, copied.2⟩
  | .grouped _ sampler _ _ => GeneralPaperEqualStoredBitSampler.observed sampler model

noncomputable def realDecode {n : ℕ} (model : RationalCostModel) (A : ℕ)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) (trace : Trace p) : Allocation n :=
  match (observed model A p trace).output with
  | none => fun _ => 0
  | some row => row.realAllocation

theorem measurable_decode {n : ℕ} (model : RationalCostModel) (A : ℕ)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) : Measurable (realDecode model A p) := by
  cases p with
  | dominant chosen heavy row correct => exact measurable_const
  | grouped small sampler hK hB =>
    change Measurable (GeneralPaperEqualFullBitDraw.realDecode sampler.categorical model sampler.address)
    exact measurable_of_countable _

theorem law {n : ℕ} (model : RationalCostModel) (A : ℕ)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    (traceLaw p).map (realDecode model A p) = outputLaw model p := by
  cases p with
  | dominant chosen heavy row correct =>
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (fun _ : Unit => (copyRow A row).1.realAllocation) (Measure.dirac ()) = Measure.dirac row.realAllocation
    rw [copy_data, Measure.map_const, measure_univ, one_smul]
  | grouped small sampler hK hB => rfl

theorem independent_players {n : ℕ} (model : RationalCostModel) (A : ℕ)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    let μ := (traceLaw p : Measure (Trace p))
    Measure.map (Prod.map (realDecode model A p) (realDecode model A p)) (μ.prod μ) =
      (outputLaw model p : Measure (Allocation n)).prod (outputLaw model p : Measure (Allocation n)) := by
  dsimp only
  rw [← law model A p]
  exact (Measure.map_prod_map _ _ (measurable_decode model A p) (measurable_decode model A p)).symm

theorem completed_ae {n : ℕ} (model : RationalCostModel) (A : ℕ)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    ∀ᵐ trace ∂(traceLaw p : Measure (Trace p)), ∃ row, (observed model A p trace).output = some row := by
  cases p with
  | dominant chosen heavy row correct => exact Filter.Eventually.of_forall (fun _ => ⟨_, rfl⟩)
  | grouped small sampler hK hB => exact GeneralPaperEqualFullBitOutput.completed_ae sampler.categorical model sampler.address

theorem completed_budget {n : ℕ} (model : RationalCostModel) (A : ℕ)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) (hB : 0 ≤ budget)
    (trace : Trace p) (row : RationalResourceArray n) (h : (observed model A p trace).output = some row) :
    FullBudget (budget : ℝ) row.realAllocation := by
  cases p with
  | dominant chosen heavy stored correct =>
    have he : (copyRow A stored).1 = row := Option.some.inj h
    rw [← he, copy_data, correct]
    exact PureBoundaryEquilibria.vertex_fullBudget _ (by exact_mod_cast hB) chosen
  | grouped small sampler hK hBudget =>
    have hb : 0 ≤ sampler.prepared.budget := by rw [hBudget]; exact hB
    have hx := GeneralPaperEqualFullBitOutput.completed_budget sampler.categorical model sampler.address
      (trace.1 + 1) (GeneralPaperEqualBooleanTraceCost.tapeFor sampler.prepared.D sampler.prepared.midpointBits trace)
      (GeneralPaperEqualRejectionTraceMeasure.scalar sampler.prepared.D sampler.prepared.midpointBits trace.1 trace.2)
      hb (GeneralPaperEqualFiniteKernel.endpoints v small) row h
    simpa only [hBudget] using hx

theorem accuracy_contract {n : ℕ} (model : RationalCostModel) (W A : ℕ) (words : BinaryAccuracyWords)
    (hOne : GeneralPaperEqualBitAccuracyDispatch.epsilon words < 1) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) (hB : 0 < budget) :
    let result := GeneralPaperEqualBitAccuracyDispatch.run model W A words values v hv budget
    let p := result.1.branch
    result.2 ≤ GeneralPaperBinaryAccuracyConstructionStorage.price A (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) +
      GeneralPaperEqualBitDispatch.bound model W A (GeneralPaperBinaryAccuracy.prepare id A words).1 values budget + 128 * A + 128 ∧
    Supported (budget : ℝ) (GeneralPaperEqualBitAccuracyDispatch.outputLaw result.1) ∧
    regret v.values (budget : ℝ) (GeneralPaperEqualBitAccuracyDispatch.outputLaw result.1)
      (GeneralPaperEqualBitAccuracyDispatch.outputLaw result.1) ≤ (GeneralPaperEqualBitAccuracyDispatch.epsilon words : ℝ) ∧
    (traceLaw p).map (realDecode model A p) = GeneralPaperEqualBitAccuracyDispatch.outputLaw result.1 ∧
    (∀ᵐ trace ∂(traceLaw p : Measure (Trace p)), ∃ row, (observed model A p trace).output = some row) ∧
    ∀ trace row, (observed model A p trace).output = some row → FullBudget (budget : ℝ) row.realAllocation := by
  let result := GeneralPaperEqualBitAccuracyDispatch.run model W A words values v hv budget
  have he := GeneralPaperEqualBitAccuracyDispatch.equilibrium model W A words hOne values v hv budget hB
  exact ⟨GeneralPaperEqualBitAccuracyDispatch.work model W A words values v hv budget, he.1, he.2,
    law model A result.1.branch, completed_ae model A result.1.branch,
    fun trace row h => completed_budget model A result.1.branch hB.le trace row h⟩

end Blotto.GeneralPaperEqualBitBranchDraw
