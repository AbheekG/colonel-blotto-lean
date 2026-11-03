import Blotto.GeneralPaperStoredNativeDrawRates

/-! Instantiate complete grouped draw rates on actual paper inputs. Every
native installed return has the expected-work component bound, and that
same majorant has the sharp input/budget/accuracy rate. No caller supplies
a storage-fit, operand-width or input-length execution oracle. -/
namespace Blotto.GeneralPaperStoredGroupedInputRates
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualInputDomain (Input)
open GeneralPaperUniformResourceGrowth
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def Grouped (model : RationalCostModel) (K : ℕ) :=
  {p : Input model // ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model (GeneralPaperEqualInputDomain.word K p)
    p.k p.values p.selector p.correct).weight j ≤ 1}

def source (model : RationalCostModel) (K : ℕ) (p : Grouped model K) :=
  GeneralPaperEqualStoredBitSampler.native true model (GeneralPaperEqualInputDomain.word K p.val) p.val.k
    p.val.values p.val.selector p.val.correct p.property p.val.budget

def width (model : RationalCostModel) (K : ℕ) (p : Grouped model K) : ℕ := (source model K p).address

def drawLog {model : RationalCostModel} {K : ℕ} (p : Grouped model K) : ℕ :=
  GeneralPaperStoredNativeReadRates.drawLog p.val

def scale {model : RationalCostModel} {K : ℕ} (p : Grouped model K) : ℕ :=
  (p.val.n + 1) * GeneralPaperEqualBitDrawRates.size p.val.n p.val.k (rationalWordWidth p.val.budget)

def majorant (model : RationalCostModel) (K : ℕ) (p : Grouped model K) : ℕ :=
  GeneralPaperStoredDrawMajorant.nativeBound model (width model K p) p.val.n p.val.k (rationalWordWidth p.val.budget)

theorem rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (majorant model K) scale drawLog := by
  let groups := fun p : Grouped model K => (GeneralPaperEqualFiniteKernel.terminal
    (GeneralPaperEqualNativeSampler.rounded true model (GeneralPaperEqualInputDomain.word K p.val)
      p.val.k p.val.values p.val.selector p.val.correct) p.property).groups.length
  have hGroups : ∀ p : Grouped model K,groups p ≤ 3 := fun p => GeneralPaperEqualNativeCache.group_count _ p.property
  have hRate := GeneralPaperStoredNativeDrawRates.native_address_rate model hFast (fun p : Grouped model K => p.val.n) groups
    (fun p => p.val.k) (fun p => rationalWordWidth p.val.budget) hGroups
  have hWidth : width model K = fun p : Grouped model K => GeneralPaperEqualBitDrawRates.address
      p.val.n (groups p) p.val.k (rationalWordWidth p.val.budget) := by
    funext p
    exact (source model K p).address_correct
  unfold majorant
  rw [hWidth]
  exact hRate

theorem component (model : RationalCostModel) (K S : ℕ) (p : Grouped model K)
    (returned : Installed (width model K p))
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S (source model K p)).values = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredAllocationLaw.observed model (width model K p) returned
        (source model K p).prepared.D (source model K p).prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law (source model K p).prepared.D (source model K p).prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive (source model K p).prepared) :
          Measure (Trace (source model K p).prepared.D (source model K p).prepared.midpointBits))) ≤
      (majorant model K p : ℝ≥0∞) :=
  GeneralPaperStoredDrawMajorant.native_expected true model (GeneralPaperEqualInputDomain.word K p.val) S p.val.k
    p.val.values p.val.selector p.val.correct p.property p.val.budget returned hReturn

end Blotto.GeneralPaperStoredGroupedInputRates
