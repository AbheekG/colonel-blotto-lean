import Blotto.GeneralPaperRetainedHeaderCountSources

/-! General stored scalar reads follow a raw header slot into the one memory.
The root, fixed prefix and index are the only addressing inputs. Scalar-kind
projections price complete copied return words. Readback is a proof premise. -/
namespace Blotto.GeneralPaperStoredScalarRead
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedFieldValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def atRoot {A B : ℕ} (installed : Installed A) (root : FixedBinaryWord B) : Installed B := ⟨installed.memory,root,0⟩

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) : Option Scalar × ℕ :=
  let pointer := GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index
  match pointer.1 with
  | none => (none,pointer.2 + 64 * A + 64)
  | some ⟨B,root⟩ =>
    let payload := GeneralPaperPayloadMemory.read B GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) root
    (payload.1,pointer.2 + payload.2 + 64 * (A + B + 1))

theorem read_ext (model : RationalCostModel) (A : ℕ) (first second : Installed A)
    (hMemory : first.memory = second.memory) (hRoot : first.root = second.root) (fixed index : ℕ) :
    read model A first fixed index = read model A second fixed index := by
  simp only [read,hMemory,hRoot]

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ)
    (root : FixedBinaryWord A) (value : Scalar)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index).1 =
      some (⟨A,root⟩ : Word))
    (hScalar : (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) root).1 = some value) :
    (read model A installed fixed index).1 = some value ∧ (read model A installed fixed index).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root fixed index).2 +
      GeneralPaperRetainedScalarValue.encode value + 192 * A + 128 := by
  change scalarMemory installed.memory root.value = some value at hScalar
  simp only [read,hPointer,GeneralPaperPayloadMemory.read,hScalar,Option.elim_some]
  constructor
  · exact True.intro
  · ring

theorem from_readback (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A)
    (hRead : Readback model A installed directory) (header : Header A) (hHeader : header ∈ directory.headers)
    (cell : Cell A) (hCell : cell ∈ directory.cells) (index : Fin header.targets.length)
    (hTarget : header.targets[index.val] = cell.region.reference) :
    (read model A (atRoot installed header.region.reference) header.fixed index.val).1 = some cell.value ∧
      (read model A (atRoot installed header.region.reference) header.fixed index.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) header.region.reference header.fixed index.val).2 +
        GeneralPaperRetainedScalarValue.encode cell.value + 192 * A + 128 := by
  have hp := hRead.1 header hHeader index
  rw [hTarget] at hp
  exact trace model A _ header.fixed index.val cell.region.reference cell.value hp (hRead.2 cell hCell).1

def rational (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) : Option ℚ × ℕ :=
  let actual := read model A installed fixed index
  match actual.1 with
  | some (.rational value) => (some value,actual.2 + rationalWordWidth value + 64 * A + 64)
  | _ => (none,actual.2 + 64 * A + 64)

def natural (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) : Option ℕ × ℕ :=
  let actual := read model A installed fixed index
  match actual.1 with
  | some (.natural value) => (some value,actual.2 + GeneralPaperEncodedScalarStorage.natBits value + 64 * A + 64)
  | _ => (none,actual.2 + 64 * A + 64)

def bit (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) : Option Bool × ℕ :=
  let actual := read model A installed fixed index
  match actual.1 with
  | some (.bit value) => (some value,actual.2 + 1 + 64 * A + 64)
  | _ => (none,actual.2 + 64 * A + 64)

theorem rational_of_scalar (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) (value : ℚ)
    (h : (read model A installed fixed index).1 = some (.rational value)) :
    (rational model A installed fixed index).1 = some value ∧ (rational model A installed fixed index).2 =
      (read model A installed fixed index).2 + rationalWordWidth value + 64 * A + 64 := by simp only [rational,h,and_self]

theorem natural_of_scalar (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) (value : ℕ)
    (h : (read model A installed fixed index).1 = some (.natural value)) :
    (natural model A installed fixed index).1 = some value ∧ (natural model A installed fixed index).2 =
      (read model A installed fixed index).2 + GeneralPaperEncodedScalarStorage.natBits value + 64 * A + 64 := by simp only [natural,h,and_self]

theorem bit_of_scalar (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed index : ℕ) (value : Bool)
    (h : (read model A installed fixed index).1 = some (.bit value)) :
    (bit model A installed fixed index).1 = some value ∧ (bit model A installed fixed index).2 =
      (read model A installed fixed index).2 + 1 + 64 * A + 64 := by simp only [bit,h,and_self]

end Blotto.GeneralPaperStoredScalarRead
