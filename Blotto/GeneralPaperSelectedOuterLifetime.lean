import Blotto.GeneralPaperOuterConstructionLifetime

/-! Actual selected outer dispatch joins both complete source-only
constructor lifetimes and the selection/result frame. Native capacities
and the full executed work majorant discharge all enclosing premises. -/
namespace Blotto.GeneralPaperSelectedOuterLifetime
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def branchWindow {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  match source with
  | ⟨.dominant chosen _ row _,A,_⟩ => GeneralPaperOuterConstructionLifetime.dominantWindow model S A chosen.val row
  | ⟨.grouped _ sampler _ _,_,_⟩ => GeneralPaperOuterConstructionLifetime.groupedWindow model S sampler

def dispatchWindow {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  fields S [S,source.address,(GeneralPaperStoredSelectedConstruction.run model S source).2] + 128 * S

def window {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  branchWindow model S source + dispatchWindow model S source

def bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperOuterConstructionLifetime.profile model S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source) +
    unit model S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source)

theorem dispatch_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    dispatchWindow model S source ≤ unit model S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source) := by
  have hPrice := GeneralPaperCompleteSelectedPreparationWork.work model W S k values v hv budget source
  have hFields := fields_bound S (natBits (cap S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source)))
    [S,source.address,(GeneralPaperStoredSelectedConstruction.run model S source).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source)) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source)
  unfold dispatchWindow
  omega

theorem branch_window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    branchWindow model S source ≤ GeneralPaperOuterConstructionLifetime.profile model S source.address
      (GeneralPaperCompleteSelectedPreparationWork.bound model S source) := by
  have hInner := GeneralPaperEqualMeasuredLayout.inner_capacity model W S k values v hv budget source
  have hTotal := GeneralPaperEqualMeasuredLayout.total_capacity model W S k values v hv budget source
  have hWidths := GeneralPaperEqualMeasuredLayout.widths_positive source
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      exact GeneralPaperOuterConstructionLifetime.dominant_bound model S A chosen.val row hWidths.2 hInner hTotal
    | grouped small sampler hK hB =>
      dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
      subst A
      exact GeneralPaperOuterConstructionLifetime.grouped_bound model S sampler hInner hTotal

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source :=
  Nat.add_le_add (branch_window_bound model W S k values v hv budget source) (dispatch_bound model W S k values v hv budget source)

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    ∃ returned : Installed source.address,(GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedConstruction.run model S source).2 ∧
      returned.work ≤ GeneralPaperCompleteSelectedPreparationWork.bound model S source ∧
      window model S source ≤ bound model S source ∧
      GeneralPaperStoredSelectedConstruction.Contract model source.address returned source.branch := by
  obtain ⟨returned,hReturn,hWork,hPrice,hContract⟩ := GeneralPaperCompleteSelectedPreparationWork.constructed model W S k values v hv budget source
  exact ⟨returned,hReturn,hWork,hPrice,window_bound model W S k values v hv budget source,hContract⟩

end Blotto.GeneralPaperSelectedOuterLifetime
