import Blotto.GeneralPaperStoredOuterReadWork

/-! Dominant and mixed-width grouped loaders charge actual address/marker
reads and pointer re-encoding. The grouped predecessor is charged once.
All metadata prices depend only on the outer address width. -/
namespace Blotto.GeneralPaperStoredDispatchLoadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def encodeBound (model : RationalCostModel) (A : ℕ) : ℕ :=
  A * GeneralPaperStoredWordEncoding.stepBound model A A (A + 1) + 64 * A + 64

def dominantBound (model : RationalCostModel) (A : ℕ) : ℕ :=
  GeneralPaperStoredOuterReadWork.addressBound model A + 2 * GeneralPaperStoredReferenceReadWork.readBound model A A +
    encodeBound model A + 1024 * (A + 1)

def groupedBound (model : RationalCostModel) (A : ℕ) : ℕ :=
  dominantBound model A + 5 * model.rat (A + 2) + 64 * (A + 1)

theorem encode_work (model : RationalCostModel) (A B : ℕ) (word : FixedBinaryWord A) (hB : B ≤ A) :
    (GeneralPaperStoredWordEncoding.word model A B word.value).2 ≤ encodeBound model A := by
  have h := GeneralPaperStoredWordEncoding.work model A B word.value (A + 1) (GeneralPaperStoredReferenceReadWork.fixed_word_width word)
  have hStep : GeneralPaperStoredWordEncoding.stepBound model A B (A + 1) ≤
      GeneralPaperStoredWordEncoding.stepBound model A A (A + 1) := by
    have hWord := binaryWordWidth_mono (Nat.add_le_add_right hB 1)
    unfold GeneralPaperStoredWordEncoding.stepBound
    omega
  have hProduct := Nat.mul_le_mul hB hStep
  unfold encodeBound
  omega

theorem dominant_work (model : RationalCostModel) (A : ℕ) (outer : Installed A) (fields : Fields A) (root : FixedBinaryWord A)
    (hRead : Readback model A outer (GeneralPaperStoredOuterDirectory.directory A fields
      (FixedBinaryWord.ofNat A root.value) (FixedBinaryWord.ofNat A 0)))
    (hRoot : outer.root = fields.record.reference) (hIndex : 3 < 2 ^ A) :
    (GeneralPaperStoredDominantOuterDraw.load model A outer).2 ≤ dominantBound model A := by
  have hAddress := GeneralPaperStoredOuterRead.address_source model A outer fields _ _ hRead hRoot
  have hAddressWork := GeneralPaperStoredOuterReadWork.address_work model A outer fields _ _ hRead hRoot hIndex
  have hMarker : (GeneralPaperStoredOuterRead.field model A outer 2).1 = some (⟨A,FixedBinaryWord.ofNat A 0⟩ : Word) :=
    GeneralPaperStoredOuterRead.field_source model A outer fields _ _ hRead hRoot ⟨2,by decide⟩
  have hPointer : (GeneralPaperStoredOuterRead.field model A outer 0).1 = some (⟨A,FixedBinaryWord.ofNat A root.value⟩ : Word) :=
    GeneralPaperStoredOuterRead.field_source model A outer fields _ _ hRead hRoot ⟨0,by decide⟩
  have hMarkerWork := GeneralPaperStoredOuterReadWork.field_work model A outer fields _ _ hRead hRoot hIndex ⟨2,by decide⟩
  have hPointerWork := GeneralPaperStoredOuterReadWork.field_work model A outer fields _ _ hRead hRoot hIndex ⟨0,by decide⟩
  change (GeneralPaperStoredOuterRead.field model A outer 2).2 ≤ _ at hMarkerWork
  change (GeneralPaperStoredOuterRead.field model A outer 0).2 ≤ _ at hPointerWork
  have hEncode := encode_work model A A (FixedBinaryWord.ofNat A root.value) le_rfl
  rw [FixedBinaryWord.value_ofNat A root.value (GeneralPaperStoredGroupedLoad.word_bound root)] at hEncode
  simp only [GeneralPaperStoredDominantOuterDraw.load,hAddress.1,hMarker,FixedBinaryWord.value_ofNat A 0 (Nat.two_pow_pos A),
    ite_true,hPointer,FixedBinaryWord.value_ofNat A root.value (GeneralPaperStoredGroupedLoad.word_bound root)]
  unfold dominantBound
  omega

theorem grouped_work (model : RationalCostModel) (I : ℕ) (outer : Installed (I + 1)) (fields : Fields (I + 1)) (root : FixedBinaryWord I)
    (hRead : Readback model (I + 1) outer (GeneralPaperStoredOuterDirectory.directory (I + 1) fields
      (FixedBinaryWord.ofNat (I + 1) root.value) (FixedBinaryWord.ofNat (I + 1) 1)))
    (hRoot : outer.root = fields.record.reference) (hIndex : 3 < 2 ^ (I + 1)) (hFuel : I + 1 < 2 ^ (I + 1)) :
    (GeneralPaperStoredGroupedLoad.load model (I + 1) outer).2 ≤ groupedBound model (I + 1) := by
  have hAddress := GeneralPaperStoredOuterRead.address_source model (I + 1) outer fields _ _ hRead hRoot
  have hAddressWork := GeneralPaperStoredOuterReadWork.address_work model (I + 1) outer fields _ _ hRead hRoot hIndex
  have hMarker : (GeneralPaperStoredOuterRead.field model (I + 1) outer 2).1 = some (⟨I + 1,FixedBinaryWord.ofNat (I + 1) 1⟩ : Word) :=
    GeneralPaperStoredOuterRead.field_source model (I + 1) outer fields _ _ hRead hRoot ⟨2,by decide⟩
  have hPointer : (GeneralPaperStoredOuterRead.field model (I + 1) outer 0).1 = some (⟨I + 1,FixedBinaryWord.ofNat (I + 1) root.value⟩ : Word) :=
    GeneralPaperStoredOuterRead.field_source model (I + 1) outer fields _ _ hRead hRoot ⟨0,by decide⟩
  have hMarkerWork := GeneralPaperStoredOuterReadWork.field_work model (I + 1) outer fields _ _ hRead hRoot hIndex ⟨2,by decide⟩
  have hPointerWork := GeneralPaperStoredOuterReadWork.field_work model (I + 1) outer fields _ _ hRead hRoot hIndex ⟨0,by decide⟩
  change (GeneralPaperStoredOuterRead.field model (I + 1) outer 2).2 ≤ _ at hMarkerWork
  change (GeneralPaperStoredOuterRead.field model (I + 1) outer 0).2 ≤ _ at hPointerWork
  have hFits : root.value < 2 ^ (I + 1) := (GeneralPaperStoredGroupedLoad.word_bound root).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ I))
  have hEncode := encode_work model (I + 1) I (FixedBinaryWord.ofNat (I + 1) root.value) (by omega)
  rw [FixedBinaryWord.value_ofNat (I + 1) root.value hFits] at hEncode
  have hPrevious := GeneralPaperStoredFreshWork.previous_work model (I + 1) (I + 1) hFuel
  simp only [GeneralPaperStoredFreshCollect.previous] at hPrevious
  have hPred : I + 1 - 1 = I := by omega
  rw [hPred] at hPrevious
  simp only [GeneralPaperStoredGroupedLoad.load,hAddress.1,hMarker,FixedBinaryWord.value_ofNat (I + 1) 1 (by omega),ite_true,
    hPointer,FixedBinaryWord.value_ofNat (I + 1) root.value hFits,GeneralPaperStoredFreshCollect.previous,hPred]
  change (GeneralPaperStoredWordEncoding.word model (I + 1) (I + 1 - 1) root.value).2 ≤ encodeBound model (I + 1) at hEncode
  unfold groupedBound dominantBound
  omega

end Blotto.GeneralPaperStoredDispatchLoadWork
