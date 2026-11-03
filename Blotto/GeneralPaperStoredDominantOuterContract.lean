import Blotto.GeneralPaperStoredDominantOuterConstruction

/-! Native dominant capacities and canonical continuous law are joined to
that actual constructor return. Hard budgets concern every returned row;
the draw takes no dimension, source-value callback or random input. -/
namespace Blotto.GeneralPaperStoredDominantOuterContract
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

noncomputable def realDecode (n : ℕ) (model : RationalCostModel) (A : ℕ) (returned : Installed A) : Allocation n :=
  match (GeneralPaperStoredDominantOuterDraw.run model A returned).values with
  | none => fun _ => 0
  | some row => fun j => (row.getD j.val 0 : ℝ)

noncomputable def outputLaw (n : ℕ) (model : RationalCostModel) (A : ℕ) (returned : Installed A) : Mixed n :=
  PureBoundaryEquilibria.pointLaw (realDecode n model A returned)

theorem law_source {n : ℕ} (model : RationalCostModel) (A : ℕ) (returned : Installed A) (row : RationalResourceArray n)
    (hRead : (GeneralPaperStoredDominantOuterDraw.run model A returned).values = some row.data) :
    outputLaw n model A returned = PureBoundaryEquilibria.pointLaw row.realAllocation := by
  unfold outputLaw realDecode
  simp only [hRead]
  rw [GeneralPaperStoredAllocationLaw.array_real]

theorem bounds {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) :
    0 < a.address ∧ (GeneralPaperStoredDominantCursor.plan model S a.address chosen.val row).sizes.sum < 2 ^ a.address ∧
      (GeneralPaperStoredDominantCursor.plan model S a.address chosen.val row).sizes.sum +
        (GeneralPaperEqualMeasuredSelectedPlan.header model S a.address).sizes.sum < 2 ^ a.address := by
  have hI := GeneralPaperEqualMeasuredLayout.inner_capacity model W S k values v hv budget a
  have hT := GeneralPaperEqualMeasuredLayout.total_capacity model W S k values v hv budget a
  dsimp only [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredLayout.innerWidth,
    GeneralPaperEqualMeasuredLayout.outer] at hI hT
  rw [hBranch] at hI hT
  exact ⟨(GeneralPaperEqualMeasuredLayout.widths_positive a).2,hI,hT⟩

theorem every_returned {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct)
    (returned : Installed a.address)
    (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned) :
    (GeneralPaperStoredDominantOuterDraw.run model a.address returned).values = some row.data ∧
      (GeneralPaperStoredDominantOuterDraw.run model a.address returned).count = n := by
  obtain ⟨hA,hI,hT⟩ := bounds model W S k values v hv budget a chosen heavy row correct hBranch
  exact GeneralPaperStoredDominantOuterConstruction.every_returned model S a.address chosen.val row hA hI hT returned hReturn

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) :
    ∃ returned : Installed a.address,
      (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned ∧
      (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).remaining = [] ∧
      returned.work = (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).work ∧
      (GeneralPaperStoredDominantOuterDraw.run model a.address returned).values = some row.data ∧
      (GeneralPaperStoredDominantOuterDraw.run model a.address returned).count = n := by
  obtain ⟨hA,hI,hT⟩ := bounds model W S k values v hv budget a chosen heavy row correct hBranch
  exact GeneralPaperStoredDominantOuterConstruction.source model S a.address chosen.val row hA hI hT

theorem native_law {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct)
    (returned : Installed a.address)
    (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned) :
    outputLaw n model a.address returned = GeneralPaperEqualSelectedSampler.outputLaw model a := by
  rw [law_source model a.address returned row (every_returned model W S k values v hv budget a chosen heavy row correct hBranch returned hReturn).1]
  change _ = GeneralPaperEqualBitBranch.outputLaw model a.branch
  rw [hBranch]
  rfl

theorem completed_budget {n : ℕ} (model : RationalCostModel) (A : ℕ) (returned : Installed A)
    (source : RationalResourceArray n) (chosen : Fin n) (budget : ℚ) (hBudget : 0 ≤ budget)
    (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hRead : (GeneralPaperStoredDominantOuterDraw.run model A returned).values = some source.data)
    (row : Array ℚ) (hOutput : (GeneralPaperStoredDominantOuterDraw.run model A returned).values = some row) :
    row.size = n ∧ FullBudget (budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) := by
  have hEq : row = source.data := Option.some.inj (hOutput.symm.trans hRead)
  rw [hEq,GeneralPaperStoredAllocationLaw.array_real,correct]
  exact ⟨source.size,PureBoundaryEquilibria.vertex_fullBudget _ (by exact_mod_cast hBudget) chosen⟩

end Blotto.GeneralPaperStoredDominantOuterContract
