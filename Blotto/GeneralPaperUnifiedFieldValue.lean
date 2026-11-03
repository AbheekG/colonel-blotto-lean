import Blotto.GeneralPaperFieldDirectorySeparation

/-! One paper RAM cell contains a reference word or a scalar payload. Cell
kinds and word widths are semantic schema annotations, not additional encoded
per-cell tags. Both typed read views are projections of this SAME address
map; no independent banks are postulated. Host/C representation is not claimed. -/
namespace Blotto.GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperRetainedScalarValue (Scalar)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

inductive Value where
  | reference : Word → Value
  | scalar : Scalar → Value

def encode : Value → ℕ
  | .reference word => word.1
  | .scalar scalar => GeneralPaperRetainedScalarValue.encode scalar

def reference : Value → Option Word
  | .reference word => some word
  | .scalar _ => none

def scalar : Value → Option Scalar
  | .reference _ => none
  | .scalar scalar => some scalar

abbrev Memory := GeneralPaperPayloadMemory.Memory Value

def referenceMemory (memory : Memory) : GeneralPaperPayloadMemory.Memory Word := fun key => (memory key).bind reference
def scalarMemory (memory : Memory) : GeneralPaperPayloadMemory.Memory Scalar := fun key => (memory key).bind scalar

theorem reference_at (memory : Memory) (key : ℕ) (word : Word) (h : memory key = some (.reference word)) :
    referenceMemory memory key = some word := by simp only [referenceMemory,h,Option.bind_some,reference]

theorem scalar_at (memory : Memory) (key : ℕ) (value : Scalar) (h : memory key = some (.scalar value)) :
    scalarMemory memory key = some value := by simp only [scalarMemory,h,Option.bind_some,scalar]

theorem reference_excludes_scalar (memory : Memory) (key : ℕ) (word : Word)
    (h : referenceMemory memory key = some word) : scalarMemory memory key = none := by
  cases hm : memory key with
  | none => simp only [referenceMemory,hm,Option.bind_none] at h; cases h
  | some value =>
    cases value with
    | reference word => simp only [scalarMemory,hm,Option.bind_some,scalar]
    | scalar scalar => simp only [referenceMemory,hm,Option.bind_some,reference] at h; cases h

theorem scalar_excludes_reference (memory : Memory) (key : ℕ) (value : Scalar)
    (h : scalarMemory memory key = some value) : referenceMemory memory key = none := by
  cases hm : memory key with
  | none => simp only [scalarMemory,hm,Option.bind_none] at h; cases h
  | some content =>
    cases content with
    | reference word => simp only [scalarMemory,hm,Option.bind_some,scalar] at h; cases h
    | scalar scalar => simp only [referenceMemory,hm,Option.bind_some,reference]

end Blotto.GeneralPaperUnifiedFieldValue
