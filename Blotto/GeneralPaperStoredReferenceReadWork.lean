import Blotto.GeneralPaperStoredFramedWork

/-! Actual reference-slot arithmetic and word construction have explicit
metadata bounds. No payload precision is charged by these bounds; the
returned reference word's own width is charged separately. -/
namespace Blotto.GeneralPaperStoredReferenceReadWork
open GeneralPaperNaturalScalarStep (word)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def envelope (L : ℕ) := 8 * (L + 1)

def slotBound (model : RationalCostModel) (S A L : ℕ) : ℕ :=
  5 * (5 * model.rat (envelope L) + 16 * S + 16) +
  A * GeneralPaperStoredWordEncoding.stepBound model S A (envelope L) + 64 * S + 64 + A + 64 * (S + A + 1)

theorem slot_widths (A base fixed stride index cell L : ℕ)
    (hA : binaryWordWidth A ≤ L) (hBase : binaryWordWidth base ≤ L) (hFixed : binaryWordWidth fixed ≤ L)
    (hStride : binaryWordWidth stride ≤ L) (hIndex : binaryWordWidth index ≤ L) (hCell : binaryWordWidth cell ≤ L) :
    word A ≤ envelope L ∧ word base ≤ envelope L ∧ word fixed ≤ envelope L ∧ word stride ≤ envelope L ∧
      word index ≤ envelope L ∧ word cell ≤ envelope L ∧ word (stride * index) ≤ envelope L ∧
      word (fixed + stride * index) ≤ envelope L ∧ word (fixed + stride * index + cell) ≤ envelope L ∧
      word (A * (fixed + stride * index + cell)) ≤ envelope L ∧
      word (base + A * (fixed + stride * index + cell)) ≤ envelope L := by
  have h0 := binaryWordWidth_mul stride index
  have h1 := GeneralPaperRayOperandWidthEnvelope.word_add fixed (stride * index)
  have h2 := GeneralPaperRayOperandWidthEnvelope.word_add (fixed + stride * index) cell
  have h3 := binaryWordWidth_mul A (fixed + stride * index + cell)
  have h4 := GeneralPaperRayOperandWidthEnvelope.word_add base (A * (fixed + stride * index + cell))
  unfold word envelope
  omega

theorem slot_work (model : RationalCostModel) (S A base fixed stride index cell L : ℕ) (target : FixedBinaryWord A)
    (hA : binaryWordWidth A ≤ L) (hBase : binaryWordWidth base ≤ L) (hFixed : binaryWordWidth fixed ≤ L)
    (hStride : binaryWordWidth stride ≤ L) (hIndex : binaryWordWidth index ≤ L) (hCell : binaryWordWidth cell ≤ L) :
    (GeneralPaperReferenceSlotConstruction.run model S A base fixed stride index cell target).2 ≤ slotBound model S A L := by
  obtain ⟨bA,bBase,bFixed,bStride,bIndex,bCell,b0,b1,b2,b3,b4⟩ := slot_widths A base fixed stride index cell L hA hBase hFixed hStride hIndex hCell
  have h0 := GeneralPaperNaturalScalarStep.work model S .mul stride index (envelope L) bStride bIndex b0
  have h1 := GeneralPaperNaturalScalarStep.work model S .add fixed (stride * index) (envelope L) bFixed b0 b1
  have h2 := GeneralPaperNaturalScalarStep.work model S .add (fixed + stride * index) cell (envelope L) b1 bCell b2
  have h3 := GeneralPaperNaturalScalarStep.work model S .mul A (fixed + stride * index + cell) (envelope L) bA b2 b3
  have h4 := GeneralPaperNaturalScalarStep.work model S .add base (A * (fixed + stride * index + cell)) (envelope L) bBase b3 b4
  have h5 := GeneralPaperStoredWordEncoding.work model S A (base + A * (fixed + stride * index + cell)) (envelope L)
    (by unfold word at b4; omega)
  unfold slotBound GeneralPaperReferenceSlotConstruction.run
  dsimp only [GeneralPaperNaturalScalarStep.data,GeneralPaperNaturalScalarStep.Op.apply] at *
  omega

theorem fixed_word_width {A : ℕ} (root : FixedBinaryWord A) : binaryWordWidth root.value ≤ A + 1 :=
  binaryWordWidth_le_of_lt_pow (by omega) ((GeneralPaperStoredGroupedLoad.word_bound root).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ A)))

def readBound (model : RationalCostModel) (A B : ℕ) : ℕ :=
  A * GeneralPaperStoredWordEncoding.stepBound model A A (envelope (A + 8)) + 64 * A + 64 +
  slotBound model A A (A + 8) + B + 128 * A + 128

theorem read_work (model : RationalCostModel) (A B fixed index : ℕ)
    (memory : GeneralPaperPayloadMemory.Memory Word) (root : FixedBinaryWord A) (target : FixedBinaryWord B)
    (hFixed : fixed ≤ 64) (hIndex : index < 2 ^ A)
    (hRead : (GeneralPaperMixedReferenceRegionProgram.read model A memory root fixed index).1 = some (⟨B,target⟩ : Word)) :
    (GeneralPaperMixedReferenceRegionProgram.read model A memory root fixed index).2 ≤ readBound model A B := by
  have hA : binaryWordWidth A ≤ A + 8 := by have h := Nat.log2_le_self A; unfold binaryWordWidth; omega
  have hBase := (fixed_word_width root).trans (show A + 1 ≤ A + 8 by omega)
  have hF : binaryWordWidth fixed ≤ A + 8 := by
    have h := binaryWordWidth_mono hFixed
    have h64 : binaryWordWidth 64 = 7 := by decide
    omega
  have hI : binaryWordWidth index ≤ A + 8 := by
    have h := binaryWordWidth_le_of_lt_pow (show 0 < A + 1 by omega)
      (hIndex.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ A)))
    omega
  have hOne : binaryWordWidth 1 ≤ A + 8 := by change 1 ≤ A + 8; omega
  have hZero : binaryWordWidth 0 ≤ A + 8 := by change 1 ≤ A + 8; omega
  have hSlot := slot_work model A A root.value fixed 1 index 0 (A + 8)
    (GeneralPaperStoredWordEncoding.word model A A 0).1 hA hBase hF hOne hI hZero
  have hEncode := GeneralPaperStoredWordEncoding.work model A A 0 (envelope (A + 8)) (by change 1 ≤ _; unfold envelope; omega)
  have hMemory := hRead
  rw [GeneralPaperMixedReferenceRegionProgram.read_data] at hMemory
  unfold GeneralPaperMixedReferenceRegionProgram.read GeneralPaperPayloadMemory.read
  dsimp only
  rw [GeneralPaperReferenceSlotConstruction.location,hMemory]
  simp only [Option.elim_some,GeneralPaperMixedReferenceMemory.encode]
  unfold readBound
  omega

end Blotto.GeneralPaperStoredReferenceReadWork
