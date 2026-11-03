import Blotto.GeneralPaperEqualFullBitDraw

/-! The returned bit sampler retains the full cache, Boolean categorical
words and the local reference width derived at preparation. A draw receives
only random inputs/finite observation parameters, never a size/cost oracle. -/
namespace Blotto.GeneralPaperEqualStoredBitSampler
open MeasureTheory
open scoped BigOperators Classical ENNReal
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 900000

structure Sampler {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k) where
  prepared : GeneralPaperEqualPreparedCache.Prepared G l
  categorical : GeneralPaperEqualBooleanCache.Cache prepared
  exponent : ℕ
  exponent_correct : prepared.midpointBits = exponent + 5
  address : ℕ
  address_correct : address = GeneralPaperEqualBitDrawRates.address n m exponent (rationalWordWidth prepared.budget)

def prepare {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : GeneralPaperEqualPreparedCache.Prepared G l) (exponent : ℕ) (h : p.midpointBits = exponent + 5) : Sampler G l :=
  ⟨p, GeneralPaperEqualBooleanCache.prepare p, exponent, h,
    GeneralPaperEqualBitDrawRates.address n m exponent (rationalWordWidth p.budget), rfl⟩

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (s : Sampler G l) (model : RationalCostModel) (cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width s.prepared.D) → Bool)
    (fresh : Fin s.prepared.midpointBits → Bool) :=
  GeneralPaperEqualFullBitDraw.run s.categorical model s.address cap tape fresh

noncomputable def observed {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (s : Sampler G l) (model : RationalCostModel) (trace : Trace s.prepared.D s.prepared.midpointBits) :=
  GeneralPaperEqualFullBitDraw.observed s.categorical model s.address trace

noncomputable def outputLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (s : Sampler G l) (model : RationalCostModel) := GeneralPaperEqualFullBitDraw.outputLaw s.categorical model s.address

def native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :=
  prepare (GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget) k rfl

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) (budget : ℚ) (hB : 0 < budget) :
    let sampler := native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    Supported (budget : ℝ) (outputLaw sampler model) ∧
      regret v.values (budget : ℝ) (outputLaw sampler model) (outputLaw sampler model) ≤ (eps : ℝ) := by
  dsimp only [outputLaw]
  rw [GeneralPaperEqualFullBitDraw.outputLaw_eq]
  exact GeneralPaperEqualCachedTraceLaw.native_epsilon bits model W values v hv eps hp hOne small budget hB _ _

end Blotto.GeneralPaperEqualStoredBitSampler
