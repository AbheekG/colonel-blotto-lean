import Blotto.BinarySeedPreparationMeasured

/-! Actual validation and seed-store preparation are consumed once. The complete
preceding measured preparation record is returned with its actual store-emitter
charge, without executing a second preparation or a cost observer. -/
namespace Blotto.BinarySeedPreparationEmission
open BinarySeedPreparationSpace
set_option autoImplicit false

def prepare {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    ((Option (BinaryPRGTapeSeedBlocks.Blocks n request.request.precision × (BinarySeedLookupTree.Store × Trace)) × Trace) × ℕ) × ℕ :=
  let blocks := BinarySeedPreparationMeasured.read request seed
  match blocks.1.1 with
  | none => (((none,blocks.1.2),blocks.2+4),0)
  | some tapes =>
      let store := BinaryWordStoreMeasured.prepareMeasured tapes.choice.bits
      (((some (tapes,store.1.1),blocks.1.2),blocks.2+store.1.2+6),store.2)

theorem prepare_compat {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (prepare request seed).1 = BinarySeedPreparationMeasured.prepare request seed := by
  unfold prepare BinarySeedPreparationMeasured.prepare
  dsimp only
  cases h : (BinarySeedPreparationMeasured.read request seed).1.1 <;> rfl

theorem prepare_emission {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (prepare request seed).2 ≤ 8*(prepare request seed).1.2 := by
  unfold prepare
  dsimp only
  split
  · dsimp only; omega
  · dsimp only
    exact (BinaryWordStoreMeasured.prepareMeasured_emission _).trans (by omega)

end Blotto.BinarySeedPreparationEmission
