import Blotto.BinaryPRGOutputPrimitiveWork
import Blotto.BinaryCachedGroupInputHeight

/-! The original global B-zero exhaustion table is built once on the selected
none branch. Its exact entry count and stored-word payload inventory derive
from original request fields; no lower-resource fallback is substituted.
The inventory is not an allocator/GC or complete control-work certificate. -/

namespace Blotto.BinaryPRGFallbackInventory
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryPRGResourceWork BinaryCachedGroupInputHeight

structure Inventory where
  writes : ℕ
  wordCells : ℕ
  deriving Repr, DecidableEq

def prepare {n : ℕ} (input : BinaryLottoResourceInput.Input n) : FixedArrayTable n SignedWord × Inventory :=
  let row := BinaryLottoSampler.fallback input
  (row,⟨n,BinaryStoredRowFrameWork.storedSpines (List.ofFn row.read) + n⟩)

theorem prepare_state {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    (prepare input).1 = BinaryLottoSampler.fallback input := rfl

theorem prepare_writes {n : ℕ} (input : BinaryLottoResourceInput.Input n) : (prepare input).2.writes = n := rfl

theorem prepare_canonical {n : ℕ} (input : BinaryLottoResourceInput.Input n) (hC : input.Canonical) :
    ∀ j, CanonicalWord ((prepare input).1.read j) := BinaryLottoSampler.fallback_canonical input hC

theorem fallback_height {n : ℕ} (input : BinaryLottoResourceInput.Input n) (s : ℕ) (hs : 3 ≤ s)
    (hH : RationalHeight (value input.budget) s) (j : Fin n) :
    RationalHeight (value ((prepare input).1.read j)) s := by
  rw [prepare_state,BinaryLottoSampler.fallback,FixedArrayTable.read_ofFn]
  split
  · exact hH
  · exact BinaryFactoryHeight.zero_height s hs

theorem prepare_wordCells_bound {n : ℕ} (input : BinaryLottoResourceInput.Input n) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : RationalHeight (value input.budget) s) :
    (prepare input).2.wordCells ≤ n * (2 * (1 + 2 * s) + 1) := by
  have hWidth := fun j => (prepare_canonical input hC j).2.trans (rationalWordWidth_of_height (fallback_height input s hs hH j))
  have hp := BinaryPRGOutputPrimitiveWork.storedSpines_bound (List.ofFn (prepare input).1.read) (1 + 2 * s)
    (by intro word hw; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw; exact hWidth j)
  simp only [List.length_ofFn] at hp
  change BinaryStoredRowFrameWork.storedSpines (List.ofFn (prepare input).1.read) + n ≤ _
  nlinarith

theorem request_prepare_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (prepare (resourceInput request rich)).2.writes = n ∧
      (prepare (resourceInput request rich)).2.wordCells ≤ n * (2 * (1 + 2 * inputHeight request) + 1) :=
  ⟨rfl,prepare_wordCells_bound _ (resource_canonical request rich) _ (by unfold inputHeight; omega) (budget_height request rich)⟩

end Blotto.BinaryPRGFallbackInventory
