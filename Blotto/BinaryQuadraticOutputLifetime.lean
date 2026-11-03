import Blotto.BinaryQuadraticLifetime
import Blotto.BinaryLifetimeArray
import Blotto.BinaryPRGOutputLifetime

/-! Original-budget scaling and coordinate framing use the actual quadratic
data opcode, one word array, one coordinate list and the native Boolean frame
producer. Old/native canonical bytes agree for valid stored inputs. No old
Euclidean scaling trace, work-pair array or ghost framing-observer allocation
is assigned to this data-only suffix. All reservations remain retained, and
actual borrowed budget/row/header payload and original seed are explicit. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticOutputLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open scoped BigOperators

def scaleData {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) : FixedArrayTable n SignedWord :=
  FixedArrayTable.ofFn (fun j => BinaryQuadraticData.apply .mul budget (row.read j))

def scaleWithTrace {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) : FixedArrayTable n SignedWord×Trace :=
  BinaryLifetimeArray.build n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul budget (row.read j))

@[simp] theorem scaleWithTrace_erases {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    (scaleWithTrace budget row).1=scaleData budget row := by
  simp only [scaleWithTrace,BinaryLifetimeArray.build_erases,BinaryQuadraticLifetime.applyWithTrace_erases,scaleData]

theorem scaleData_state {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord)
    (hB : BinaryRationalOpcode.Valid budget) (hR : ∀ j,BinaryRationalOpcode.Valid (row.read j)) :
    scaleData budget row=BinaryPRGOriginalSampler.rescale budget row := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [scaleData,BinaryPRGOriginalSampler.rescale,FixedArrayTable.read_ofFn]
  rw [← BinaryQuadraticData.apply_erasure]
  exact BinaryQuadraticOpcode.applyWithWork_state .mul budget (row.read j) hB (hR j)

theorem scaleWithTrace_bounds {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) (W : ℕ)
    (hB : width budget≤W) (hR : ∀ j,width (row.read j)≤W) :
    listCells (scaleWithTrace budget row).2+arraySlots (scaleWithTrace budget row).2≤
      n*BinaryQuadraticLifetime.opcodeBound W+2*(n+1)^2+8 ∧
    framePeak (scaleWithTrace budget row).2≤n+BinaryQuadraticLifetime.opcodeFrames W+6 :=
  BinaryLifetimeArray.build_bounds n _ (BinaryQuadraticLifetime.opcodeBound W) (BinaryQuadraticLifetime.opcodeFrames W)
    (fun j => (BinaryQuadraticLifetime.applyWithTrace_bounds .mul budget (row.read j) W hB (hR j)).1)
    (fun j => (BinaryQuadraticLifetime.applyWithTrace_bounds .mul budget (row.read j) W hB (hR j)).2)

theorem scaleData_width {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (hRV : ∀ j,BinaryRationalOpcode.Valid (row.read j))
    (W : ℕ) (hB : width budget≤W) (hR : ∀ j,width (row.read j)≤W) :
    ∀ j,width ((scaleData budget row).read j)≤3*W+1 := by
  intro j
  rw [scaleData_state budget row hBV hRV]
  simp only [BinaryPRGOriginalSampler.rescale,FixedArrayTable.read_ofFn]
  exact (BinaryPRGPreparationWork.apply_stored_width .mul budget (row.read j)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le hB (hR j))) 1)

def outputData {n : ℕ} (budget : SignedWord) (header : List Bool) (row : FixedArrayTable n SignedWord) : List Bool :=
  header++BinaryStoredRowFrame.words (List.ofFn (scaleData budget row).read)

def outputWithTrace {n : ℕ} (budget : SignedWord) (header : List Bool) (row : FixedArrayTable n SignedWord) : List Bool×Trace :=
  let scaled := scaleWithTrace budget row
  let inputs := List.ofFn scaled.1.read
  let framed := BinaryPRGOutputLifetime.frameWithTrace header inputs
  (framed.1,[.frames (n+8),.listAllocation n,.arrayAllocation 8] ++ under 2 scaled.2 ++ under 2 framed.2)

@[simp] theorem outputWithTrace_erases {n : ℕ} (budget : SignedWord) (header : List Bool) (row : FixedArrayTable n SignedWord) :
    (outputWithTrace budget header row).1=outputData budget header row := by
  simp only [outputWithTrace,BinaryPRGOutputLifetime.frameWithTrace_state,scaleWithTrace_erases,outputData]

def bound (n W headerLength : ℕ) : ℕ :=
  n*BinaryQuadraticLifetime.opcodeBound W+2*(n+1)^2+16+n+headerLength+3*n*(12*W+7)
def frames (n W headerLength : ℕ) : ℕ :=
  BinaryQuadraticLifetime.opcodeFrames W+headerLength+3*n+n*(12*W+7)+20

theorem outputWithTrace_bounds {n : ℕ} (budget : SignedWord) (header : List Bool) (row : FixedArrayTable n SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (hRV : ∀ j,BinaryRationalOpcode.Valid (row.read j))
    (W : ℕ) (hB : width budget≤W) (hR : ∀ j,width (row.read j)≤W) :
    listCells (outputWithTrace budget header row).2+arraySlots (outputWithTrace budget header row).2≤bound n W header.length ∧
    framePeak (outputWithTrace budget header row).2≤frames n W header.length := by
  let inputs := List.ofFn (scaleData budget row).read
  have hScale := scaleWithTrace_bounds budget row W hB hR
  have hWidths := scaleData_width budget row hBV hRV W hB hR
  have hWords := BinaryPRGOutputLifetime.words_length_bound inputs (3*W+1)
    (by intro word hm; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm; exact hWidths j)
  simp only [inputs,List.length_ofFn] at hWords
  rw [show 4*(3*W+1)+3=12*W+7 by omega] at hWords
  have hFrame := BinaryPRGOutputLifetime.frameWithTrace_cells header inputs
  have hFramePeak := BinaryPRGOutputLifetime.frameWithTrace_frames header inputs
  have hScaleFrames := framePeak_under 2 (scaleWithTrace budget row).2
  have hFramedFrames := framePeak_under 2 (BinaryPRGOutputLifetime.frameWithTrace header inputs).2
  simp only [inputs,List.length_ofFn] at hFramePeak
  unfold outputWithTrace bound frames
  simp only [scaleWithTrace_erases,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under,BinaryPRGOutputLifetime.frameWithTrace_arrays]
  dsimp only [inputs] at hFrame hFramePeak hFramedFrames
  exact ⟨by nlinarith only [hScale.1,hFrame,hWords],by omega⟩

def rowCells {n : ℕ} (row : FixedArrayTable n SignedWord) : ℕ := 4+n+∑ j,BinaryRationalOpcodeAllocation.payload (row.read j)

theorem all_prefix_heap {n : ℕ} (budget : SignedWord) (header : List Bool) (row : FixedArrayTable n SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (hRV : ∀ j,BinaryRationalOpcode.Valid (row.read j))
    (W : ℕ) (hB : width budget≤W) (hR : ∀ j,width (row.read j)≤W)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (BinaryRationalOpcodeAllocation.payload budget+header.length+rowCells row+originalSeedCells+borrowedOtherCells)
      (outputWithTrace budget header row).2 steps≤
      BinaryRationalOpcodeAllocation.payload budget+header.length+rowCells row+originalSeedCells+borrowedOtherCells+
        bound n W header.length :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (outputWithTrace_bounds budget header row hBV hRV W hB hR).1

theorem all_prefix_frames {n : ℕ} (budget : SignedWord) (header : List Bool) (row : FixedArrayTable n SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (hRV : ∀ j,BinaryRationalOpcode.Valid (row.read j))
    (W : ℕ) (hB : width budget≤W) (hR : ∀ j,width (row.read j)≤W) (steps : ℕ) :
    framePeak ((outputWithTrace budget header row).2.take steps)≤frames n W header.length :=
  (framePeak_take_le _ _).trans (outputWithTrace_bounds budget header row hBV hRV W hB hR).2

end Blotto.BinaryQuadraticOutputLifetime
