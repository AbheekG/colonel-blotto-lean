import Blotto.GeneralPaperEqualDescriptionRates
import Blotto.RationalRawGroupRouting
import Blotto.GeneralPaperNativeQuantizedLabels

/-! The equal-budget constructor shares the packed group table between its
routes and small segment formula, and shares the integer denominator between
all count entries. Exact returned-data equality transfers all existing sampler
contracts. Preparation prices and live-space windows are separate obligations. -/
namespace Blotto.GeneralPaperEqualCachedPreparation
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (compact count)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem output_eq {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    p.prepareOutput = PreparedGroupOutput.prepare i.partition := by
  have ht := GeneralPaperNativeQuantizedLabels.table_ext p.prepareOutput.table i.partition.routes p.prepareOutput.correct
  cases h : p.prepareOutput with
  | mk table correct =>
    rw [h] at ht
    change table = i.partition.routes at ht
    cases ht
    rfl

def cache {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (K : ℕ) (budget : ℚ) : Prepared (terminal v small).partition (lottery v small) :=
  let i := terminal v small
  let packed := RationalTerminalPacking.prepare i
  let source := (packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery i.groups_count
  let segments := PreparedSegmentDescriptor.prepare (compact source)
  let D := GeneralPaperEqualCategoricalIntegerData.denominator segments.lottery.weight
  let counts := FixedArrayTable.ofFn (fun j =>
    (segments.weights.read j).num.toNat * (D / (segments.weights.read j).den))
  let power := GeneralPaperNatPower.run 2 K
  ⟨packed.prepareOutput, segments, D, rfl, counts, (by intro j; exact FixedArrayTable.read_ofFn _ j),
    UniformNatRejection.width D, rfl, K, power.power, (GeneralPaperNatPower.data 2 K).1, budget⟩

theorem cache_eq {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (K : ℕ) (budget : ℚ) :
    cache v small K budget = GeneralPaperEqualPreparedCache.prepare (terminal v small).partition (lottery v small) K budget := by
  unfold cache GeneralPaperEqualPreparedCache.prepare
  dsimp only
  rw [output_eq]
  rfl

theorem sampler_eq {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p q : Prepared G l) (k : ℕ) (hp : p.midpointBits = k + 5) (hq : q.midpointBits = k + 5) (h : p = q) :
    GeneralPaperEqualStoredBitSampler.prepare p k hp = GeneralPaperEqualStoredBitSampler.prepare q k hq := by
  cases h
  rfl

def native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) :=
  let raw := (GeneralPaperValueRoundingPaperContract.run bits model W 128 k values).1
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 128 k (by decide) values v hv
  let rounded := GeneralPaperNativeRationalValues.selector raw.2 hp.1 raw.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 k values)
  let prepared := cache rounded small (k + 5) budget
  GeneralPaperEqualStoredBitSampler.prepare prepared k rfl

theorem native_eq {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) :
    native bits model W k values v hv small budget =
      GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget := by
  unfold native
  dsimp only
  change GeneralPaperEqualStoredBitSampler.prepare
    (cache (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small (k + 5) budget) k rfl = _
  have hCache := cache_eq (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small (k + 5) budget
  exact sampler_eq _ _ k rfl rfl hCache

end Blotto.GeneralPaperEqualCachedPreparation
