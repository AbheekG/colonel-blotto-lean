import Blotto.GeneralPaperStoredBooleanWordRead

/-! A retained word is read through its actual record pointer and the stored
bit-list count. The source word occurs only in this erased correspondence;
execution uses the same installed memory throughout. -/
namespace Blotto.GeneralPaperStoredBooleanWordSourceRead
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def parent {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedBinaryWord w) : Header A :=
  ⟨(GeneralPaperBooleanWordCursor.expected model S A source start).root,0,
    [(GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits).root.reference]⟩

theorem headers {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedBinaryWord w) :
    (GeneralPaperBooleanWordCursor.expected model S A source start).headers =
      (GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits).headers ++ [parent model S A start source] := by
  simp only [GeneralPaperBooleanWordCursor.expected,GeneralPaperTrailingDirectoryRecord.expected,
    GeneralPaperTrailingDirectoryRecord.compose,GeneralPaperChildDirectorySpecification.collect,
    GeneralPaperChildDirectorySpecification.directories,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,parent]

theorem cells {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedBinaryWord w) :
    (GeneralPaperBooleanWordCursor.expected model S A source start).cells =
      (GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits).cells := by
  simp only [GeneralPaperBooleanWordCursor.expected,GeneralPaperTrailingDirectoryRecord.expected,
    GeneralPaperTrailingDirectoryRecord.compose,GeneralPaperChildDirectorySpecification.collect,
    GeneralPaperChildDirectorySpecification.directories,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil]

theorem source {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (full : Directory A) (hContract : Contract model A installed full) (word : FixedBinaryWord w)
    (hRead : Readback model A installed (GeneralPaperBooleanWordCursor.expected model S A word start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanWordCursor.expected model S A word start).root.reference) :
    (GeneralPaperStoredBooleanWordRead.read model A installed).1 = some (⟨w,word⟩ : Word) ∧
      (GeneralPaperStoredBooleanWordRead.read model A installed).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 0).2 +
        (GeneralPaperStoredBooleanWordRead.packed model A
          (GeneralPaperStoredScalarRead.atRoot installed (GeneralPaperBooleanWordCursor.bitsExpected model S A start word.bits).root.reference)).2 +
        128 * A + 64 := by
  let child := GeneralPaperBooleanWordCursor.bitsExpected model S A start word.bits
  have hParent : parent model S A start word ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).headers := by
    rw [headers]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hPointer := hRead.1 (parent model S A start word) hParent ⟨0,by change 0 < 1; decide⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory)
    (GeneralPaperBooleanWordCursor.expected model S A word start).root.reference 0 0).1 = some (⟨A,child.root.reference⟩ : Word) at hPointer
  rw [← hRoot] at hPointer
  have hChildHeaders : ∀ header ∈ child.headers,header ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).headers := by
    intro header hh
    rw [headers]
    exact List.mem_append_left _ hh
  have hChildCells : ∀ cell ∈ child.cells,cell ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).cells := by
    intro cell hc
    rw [cells]
    exact hc
  have hChildRead : Readback model A (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) child :=
    GeneralPaperHeaderCountReadback.restrict model A installed _ child hRead hChildHeaders hChildCells
  have hChildContract : Contract model A (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) full := hContract
  have hBitHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 2 (word.bits.map Scalar.bit) ∈ full.headers := by
    apply hHeaders
    apply hChildHeaders
    exact List.mem_singleton_self _
  have hWord := GeneralPaperStoredBooleanWordRead.bits_source model S A start
    (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) full hChildContract word hChildRead hBitHeader rfl
  exact GeneralPaperStoredBooleanWordRead.trace model A installed child.root.reference ⟨w,word⟩ hPointer hWord.1

end Blotto.GeneralPaperStoredBooleanWordSourceRead
