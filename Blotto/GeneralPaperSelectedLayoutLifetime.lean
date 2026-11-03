import Blotto.GeneralPaperLayoutLifetimeRates

/-! Join the actual selected temporary-data owner window to both complete
layout activation/scratch reserves and their parent frame. Positivity and
capacity come from the same native selected source. Other preparation-pass
frames and caller/installed-memory coexistence remain separate obligations. -/
namespace Blotto.GeneralPaperSelectedLayoutLifetime
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def window {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperSelectedTemporaryOwners.window model S source +
    GeneralPaperTwoPoolLayoutLifetime.window model S (innerWidth source) source.address
      (inner model S source) (outer model S source)

def bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperSelectedTemporaryOwners.bound model S source +
    GeneralPaperTwoPoolLayoutLifetime.bound model S (innerWidth source) source.address
      (inner model S source).sizes.sum (outer model S source).sizes.sum
      (GeneralPaperCompleteSelectedPreparationWork.bound model S source)

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hOwners := GeneralPaperSelectedTemporaryOwners.window_bound model W S k values v hv budget source
  have hWidths := widths_positive source
  have hInner := GeneralPaperSelectedTemporaryOwners.inner_good model S source
  have hOuter := GeneralPaperMeasuredRetainedPlanWork.header model S source.address hWidths.2
  have hFrames := GeneralPaperTwoPoolLayoutLifetime.window_bound model S (innerWidth source) source.address
    (GeneralPaperCompleteSelectedPreparationWork.bound model S source)
    (inner model S source) (outer model S source) hInner.1 hOuter.1 hWidths.1 hWidths.2
    (inner_capacity model W S k values v hv budget source) (total_capacity model W S k values v hv budget source)
    (GeneralPaperSelectedTemporaryOwners.layout_price model W S k values v hv budget source)
  exact Nat.add_le_add hOwners hFrames

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    ∃ returned : Installed source.address,
      (GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedConstruction.run model S source).2 ∧
      returned.work ≤ GeneralPaperCompleteSelectedPreparationWork.bound model S source ∧
      window model S source ≤ bound model S source ∧
      GeneralPaperStoredSelectedConstruction.Contract model source.address returned source.branch := by
  obtain ⟨returned,hReturn,hWork,hPrice,hContract⟩ :=
    GeneralPaperCompleteSelectedPreparationWork.constructed model W S k values v hv budget source
  exact ⟨returned,hReturn,hWork,hPrice,window_bound model W S k values v hv budget source,hContract⟩

end Blotto.GeneralPaperSelectedLayoutLifetime
