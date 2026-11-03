import Blotto.GeneralPaperEqualNativeRouteCost

/-! The cache consumes the actual measured route return. It does not rebuild
routes. Remaining segment/integer/Boolean/control/closure costs are separate;
exact equality transfers the existing sampler semantics. -/
namespace Blotto.GeneralPaperEqualRoutedCache
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (compact)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def core {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small)) (routes : PreparedGroupOutput (terminal v small).partition)
    (K : ℕ) (budget : ℚ) :
    Prepared (terminal v small).partition
      ((packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery (terminal v small).groups_count) :=
  let source := (packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery (terminal v small).groups_count
  let segments := PreparedSegmentDescriptor.prepare (compact source)
  let D := GeneralPaperEqualCategoricalIntegerData.denominator segments.lottery.weight
  let counts := FixedArrayTable.ofFn (fun j =>
    (segments.weights.read j).num.toNat * (D / (segments.weights.read j).den))
  let power := GeneralPaperNatPower.run 2 K
  ⟨routes, segments, D, rfl, counts, (by intro j; exact FixedArrayTable.read_ofFn _ j),
    UniformNatRejection.width D, rfl, K, power.power, (GeneralPaperNatPower.data 2 K).1, budget⟩

theorem core_eq {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small)) (routes : PreparedGroupOutput (terminal v small).partition)
    (hRoutes : routes = packed.prepareOutput) (K : ℕ) (budget : ℚ) :
    core v small packed routes K budget = GeneralPaperEqualPackedCache.core v small packed K budget := by
  rw [hRoutes]
  rfl

def fromPacking {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small))
    (routes : PreparedGroupOutput (terminal v small).partition) (K : ℕ) (budget : ℚ) :
    Prepared (terminal v small).partition (lottery v small) :=
  let h : ((packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery (terminal v small).groups_count) = lottery v small := by
    rw [hp]
    rfl
  cast (congrArg (Prepared (terminal v small).partition) h) (core v small packed routes K budget)

theorem fromPacking_eq {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small))
    (routes : PreparedGroupOutput (terminal v small).partition) (hRoutes : routes = packed.prepareOutput)
    (K : ℕ) (budget : ℚ) :
    fromPacking v small packed hp routes K budget = GeneralPaperEqualPackedCache.fromPacking v small packed hp K budget := by
  rw [hRoutes]
  rfl

def close {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small))
    (routes : PreparedGroupOutput (terminal v small).partition) (hRoutes : routes = packed.prepareOutput)
    (k : ℕ) (budget : ℚ) :=
  let p := fromPacking v small packed hp routes (k + 5) budget
  GeneralPaperEqualStoredBitSampler.prepare p k (by
    change (fromPacking v small packed hp routes (k + 5) budget).midpointBits = k + 5
    rw [fromPacking_eq v small packed hp routes hRoutes, GeneralPaperEqualPackedCache.fromPacking_eq]
    rfl)

theorem close_eq {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal v small))
    (hp : packed = RationalTerminalPacking.prepare (terminal v small))
    (routes : PreparedGroupOutput (terminal v small).partition) (hRoutes : routes = packed.prepareOutput)
    (k : ℕ) (budget : ℚ) :
    close v small packed hp routes hRoutes k budget = GeneralPaperEqualPackedCache.close v small packed hp k budget := by
  unfold close GeneralPaperEqualPackedCache.close
  apply GeneralPaperEqualCachedPreparation.sampler_eq
  exact fromPacking_eq v small packed hp routes hRoutes (k + 5) budget

end Blotto.GeneralPaperEqualRoutedCache
