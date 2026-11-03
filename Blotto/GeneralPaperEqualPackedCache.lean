import Blotto.GeneralPaperEqualMaterializedPacking

/-! Feed an already constructed packed table directly into both cached routes
and the small segment formula. The transport is erased; neither a packing
rerun nor a reconstructed route/formula table is hidden in the equality proof. -/
namespace Blotto.GeneralPaperEqualPackedCache
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (compact)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def core {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small)) (K : ℕ) (budget : ℚ) :
    Prepared (terminal v small).partition
      ((packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery (terminal v small).groups_count) :=
  let source := (packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery (terminal v small).groups_count
  let segments := PreparedSegmentDescriptor.prepare (compact source)
  let D := GeneralPaperEqualCategoricalIntegerData.denominator segments.lottery.weight
  let counts := FixedArrayTable.ofFn (fun j =>
    (segments.weights.read j).num.toNat * (D / (segments.weights.read j).den))
  let power := GeneralPaperNatPower.run 2 K
  ⟨packed.prepareOutput, segments, D, rfl, counts, (by intro j; exact FixedArrayTable.read_ofFn _ j),
    UniformNatRejection.width D, rfl, K, power.power, (GeneralPaperNatPower.data 2 K).1, budget⟩

def fromPacking {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small)) (K : ℕ) (budget : ℚ) :
    Prepared (terminal v small).partition (lottery v small) :=
  let h : ((packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery (terminal v small).groups_count) = lottery v small := by
    rw [hp]
    rfl
  cast (congrArg (Prepared (terminal v small).partition) h) (core v small packed K budget)

theorem fromPacking_eq {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small)) (K : ℕ) (budget : ℚ) :
    fromPacking v small packed hp K budget = GeneralPaperEqualCachedPreparation.cache v small K budget := by
  cases hp
  rfl

def close {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small)) (k : ℕ) (budget : ℚ) :=
  let p := fromPacking v small packed hp (k + 5) budget
  GeneralPaperEqualStoredBitSampler.prepare p k (by
    change (fromPacking v small packed hp (k + 5) budget).midpointBits = k + 5
    rw [fromPacking_eq]
    rfl)

theorem close_eq {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small)) (k : ℕ) (budget : ℚ) :
    close v small packed hp k budget = GeneralPaperEqualStoredBitSampler.prepare
      (GeneralPaperEqualPreparedCache.prepare (terminal v small).partition (lottery v small) (k + 5) budget) k rfl := by
  unfold close
  apply GeneralPaperEqualCachedPreparation.sampler_eq
  exact (fromPacking_eq v small packed hp (k + 5) budget).trans
    (GeneralPaperEqualCachedPreparation.cache_eq v small (k + 5) budget)

end Blotto.GeneralPaperEqualPackedCache
