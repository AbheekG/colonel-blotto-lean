import Blotto.RationalPRGCheckedTableWork
import Blotto.RationalPRGRequestWorkBound

/-! Adds parsed game count/length/table bookkeeping to the existing complete
request primitive/copy observer. Addressing, decoder-index and local sampler
metadata, physical backend/records/ownership/space remain separate. -/

namespace Blotto.RationalPRGBinaryRequest

def gameMetadataBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  RationalPRGBinaryInput.rawMetadataBitWork primitive frame + RationalPRGBinaryInput.checkedTableBitWork primitive frame

def gameMetadataBound (c length : ℕ) : ℕ :=
  RationalPRGBinaryInput.rawMetadataBound c length + RationalPRGBinaryInput.checkedTableBound c length

theorem gameMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    gameMetadataBitWork primitive frame ≤ gameMetadataBound c frame.length :=
  Nat.add_le_add (RationalPRGBinaryInput.rawMetadataBitWork_bound primitive c hPrimitive frame)
    (RationalPRGBinaryInput.checkedTableBitWork_bound primitive c hPrimitive frame)

noncomputable def executionWithGameMetadataBitWork (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionBitWork model primitive copyResources rich frame seed + gameMetadataBitWork primitive frame

theorem executionWithGameMetadataBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithGameMetadataBitWork model primitive copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length :=
  Nat.add_le_add (executionBitWork_frame_bound model primitive c hPrimitive copyResources rich frame seed)
    (gameMetadataBitWork_bound primitive c hPrimitive frame)

end Blotto.RationalPRGBinaryRequest
