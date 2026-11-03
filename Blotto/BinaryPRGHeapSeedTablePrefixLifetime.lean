import Blotto.BinaryPRGHeapSeededPrefixLifetime
import Blotto.BinaryPRGFrameCostJoin

/-! A retained choice array supplies its actual list copy, seed tree, physical
resource execution and terminal cache. Successful raw parsing derives the
source/dimension/choice-count parameters of every-prefix polynomial bounds. -/
namespace Blotto.BinaryPRGHeapSeedTablePrefixLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def runWithTrace {n N : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (choice : FixedArrayTable N Bool) :
    BinaryPRGHeapSeededPrefixLifetime.Retained request rich choice.data.toList × Trace :=
  let seed := choice.data.toList
  let later := BinaryPRGHeapSeededPrefixLifetime.runWithTrace request rich seed
  (later.1,wrapList choice.data.size 16 (choice.data.size + 2) [later.2])

theorem runWithTrace_erasure {n N : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (choice : FixedArrayTable N Bool) :
    BinaryPRGHeapSeededPrefixLifetime.erase (runWithTrace request rich choice).1 =
      BinaryPRGHeapCachedPrefixLifetime.reference (BinarySeedLookupTree.prepare choice.data.toList) request rich :=
  BinaryPRGHeapSeededPrefixLifetime.runWithTrace_erasure request rich choice.data.toList

theorem uniform_usage : ∃ C d : ℕ,∀ {n N : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (choice : FixedArrayTable N Bool),
    usage (runWithTrace request rich choice).2 ≤ C * (n + request.source.originalInputWordWidth + N + 2)^d := by
  rcases BinaryPRGHeapSeededPrefixLifetime.uniform_usage with ⟨C,d,hBound⟩
  refine ⟨C + 22,d + 1,?_⟩
  intro n N request rich choice
  have h := hBound request rich choice.data.toList
  simp only [Array.length_toList,choice.size] at h
  let X := n + request.source.originalInputWordWidth + N + 2
  have hX : 0 < X := by dsimp [X]; omega
  have hSmall : X^d ≤ X^(d + 1) := Nat.pow_le_pow_right hX (by omega)
  have hLarge : X ≤ X^(d + 1) := by simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ d + 1 by omega)
  have hOne := Nat.one_le_pow (d + 1) X hX
  have hN : N ≤ X := by dsimp [X]; omega
  have hScale := Nat.mul_le_mul_left C hSmall
  have hLinear := Nat.mul_le_mul_left 2 (hN.trans hLarge)
  have hw := wrapList_usage choice.data.size 16 (choice.data.size + 2)
    [(BinaryPRGHeapSeededPrefixLifetime.runWithTrace request rich choice.data.toList).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,choice.size] at hw
  unfold runWithTrace
  dsimp only
  simp only [choice.size]
  change _ ≤ (C + 22) * X^(d + 1)
  change _ ≤ C * X^d at h
  nlinarith

theorem uniform_all_prefix : ∃ C d : ℕ,∀ {n N : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (choice : FixedArrayTable N Bool) (borrowedOtherCells steps : ℕ),
    retainedHeap (borrowedOtherCells + N + 8) (runWithTrace request rich choice).2 steps ≤
        borrowedOtherCells + N + 8 + C * (n + request.source.originalInputWordWidth + N + 2)^d ∧
      framePeak ((runWithTrace request rich choice).2.take steps) ≤ C * (n + request.source.originalInputWordWidth + N + 2)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun request rich choice borrowed steps => BinaryPRGHeapTraceUsage.all_prefix _ _
    (hBound request rich choice) (borrowed + _ + 8) steps⟩

theorem parsed_all_prefix : ∃ C d : ℕ,∀ (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool),
    (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed →
    ∀ (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision) (rich : Bool) (borrowedOtherCells steps : ℕ),
    retainedHeap (borrowedOtherCells + RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision + 8)
        (runWithTrace parsed.1.2.request rich tables.choice).2 steps ≤
      borrowedOtherCells + RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision + 8 +
        C * (frame.length + 1)^d ∧
      framePeak ((runWithTrace parsed.1.2.request rich tables.choice).2.take steps) ≤ C * (frame.length + 1)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  refine ⟨C * 3033^d,d,?_⟩
  intro frame parsed hParsed tables rich borrowed steps
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hParsed
  have hS := BinaryPRGFrameCostJoin.read_source_width frame parsed hParsed
  have hSeed := BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed hParsed
  have hCount : RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision ≤ 8 * frame.length + 3025 := by
    have hle : RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision ≤
        RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.request.precision := by
      unfold RationalLottoResourceSystem.sampleBitBudget RationalLottoResourceSystem.innerBitBudget
      omega
    exact hle.trans hSeed
  have hSize : parsed.1.1 + parsed.1.2.request.source.originalInputWordWidth +
      RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision + 2 ≤ 3033 * (frame.length + 1) := by omega
  have h := (hBound parsed.1.2.request rich tables.choice).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d))
  rw [Nat.mul_pow] at h
  have hTop : usage (runWithTrace parsed.1.2.request rich tables.choice).2 ≤ (C * 3033^d) * (frame.length + 1)^d := by
    nlinarith
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ hTop _ steps

end Blotto.BinaryPRGHeapSeedTablePrefixLifetime
