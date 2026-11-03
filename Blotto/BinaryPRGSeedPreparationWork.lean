import Blotto.BinaryPRGBooleanSeedBlocks
import Blotto.BinaryWordStoreWork

/-! One measured preparation phase validates the actual supplied rulers and
builds the actual physical choice tree. Its typed result equals the validation
and store pair consumed by the complete traced output. Rejection never builds
the tree. -/
namespace Blotto.BinaryPRGSeedPreparationWork
open BinaryPRGTapeSeedBlocks BinaryPRGBooleanSeedBlocks BinarySeedLookupTree RationalLottoResourceSystem

def tracedResult {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    Option (Blocks n prepared.request.precision × Store) :=
  (readWithTrace prepared seed).1.map
    (fun blocks => (blocks,(BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1))

def prepareWithWork {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    Option (Blocks n prepared.request.precision × Store) × ℕ :=
  let blocks := readWithWork prepared seed
  match blocks.1 with
  | none => (none,blocks.2+4)
  | some tapes =>
      let store := BinaryWordStoreWork.prepareWithWork tapes.choice.bits
      (some (tapes,store.1),blocks.2+store.2+6)

theorem prepare_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (prepareWithWork prepared seed).1 = tracedResult prepared seed := by
  unfold prepareWithWork tracedResult
  dsimp only
  rw [read_work_state]
  cases h : (readWithTrace prepared seed).1 with
  | none => rfl
  | some tapes => simp only [Option.map_some,BinaryWordStoreWork.prepare_state]

theorem prepare_work {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (prepareWithWork prepared seed).2 ≤
      42*sampleBitBudget n prepared.request.precision+40 := by
  have hb := read_work prepared seed
  unfold prepareWithWork
  dsimp only
  split
  · omega
  · rename_i tapes hTapes
    have hStore := BinaryWordStoreWork.prepare_work tapes.choice.bits
    have hChoice : tapes.choice.bits.length = coinBitBudget n prepared.request.precision := tapes.choice.size
    have hN : coinBitBudget n prepared.request.precision ≤
        sampleBitBudget n prepared.request.precision := by
      unfold sampleBitBudget innerBitBudget
      omega
    omega

end Blotto.BinaryPRGSeedPreparationWork
