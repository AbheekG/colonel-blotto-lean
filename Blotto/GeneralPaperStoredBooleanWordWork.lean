import Blotto.GeneralPaperStoredBitCollectionWork

/-! A stored Boolean word is reconstructed once through actual count/bit
reads. The record parent and selected bit owner lie in the same enclosing
memory. Complete work is linear in word length up to address metadata. -/
namespace Blotto.GeneralPaperStoredBooleanWordWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperUnifiedFieldValue (referenceMemory)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def packedBound (model : RationalCostModel) (A w : ℕ) : ℕ :=
  GeneralPaperStoredBitCollectionWork.bound model A w + GeneralPaperEncodedScalarStorage.natBits w + 64 * (A + 1)

def bound (model : RationalCostModel) (A w : ℕ) : ℕ :=
  packedBound model A w + GeneralPaperStoredReferenceReadWork.readBound model A A + 128 * A + 64

theorem packed_work {w : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed) (word : FixedBinaryWord w)
    (hRead : Readback model A installed (GeneralPaperBooleanWordCursor.bitsExpected model S A start word.bits))
    (hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 2 (word.bits.map Scalar.bit) ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanWordCursor.bitsExpected model S A start word.bits).root.reference) :
    (GeneralPaperStoredBooleanWordRead.packed model A installed).2 ≤ packedBound model A w := by
  have hBits := GeneralPaperStoredBitCollectionWork.work model S A layoutStart start plan full installed ctx word.bits hRead hHeader hRoot
  rw [word.size] at hBits
  rw [(GeneralPaperStoredBooleanWordRead.bits_source model S A start installed full ctx.contract word hRead hHeader hRoot).2]
  exact Nat.add_le_add_right (Nat.add_le_add_right hBits (GeneralPaperEncodedScalarStorage.natBits w)) (64 * (A + 1))

theorem work {w : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed) (word : FixedBinaryWord w)
    (hRead : Readback model A installed (GeneralPaperBooleanWordCursor.expected model S A word start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanWordCursor.expected model S A word start).root.reference) :
    (GeneralPaperStoredBooleanWordRead.read model A installed).2 ≤ bound model A w := by
  let child := GeneralPaperBooleanWordCursor.bitsExpected model S A start word.bits
  let parent := GeneralPaperStoredBooleanWordSourceRead.parent model S A start word
  have hParent : parent ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).headers := by
    rw [GeneralPaperStoredBooleanWordSourceRead.headers]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hPointer := hRead.1 parent hParent ⟨0,by change 0 < 1; decide⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory)
    (GeneralPaperBooleanWordCursor.expected model S A word start).root.reference 0 0).1 =
      some (⟨A,child.root.reference⟩ : GeneralPaperMixedReferenceMemory.Word) at hPointer
  rw [← hRoot] at hPointer
  have hChildHeaders : ∀ header ∈ child.headers,header ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).headers := by
    intro header hh
    rw [GeneralPaperStoredBooleanWordSourceRead.headers]
    exact List.mem_append_left _ hh
  have hChildCells : ∀ cell ∈ child.cells,cell ∈ (GeneralPaperBooleanWordCursor.expected model S A word start).cells := by
    intro cell hc
    rw [GeneralPaperStoredBooleanWordSourceRead.cells]
    exact hc
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildRead : Readback model A loaded child :=
    GeneralPaperHeaderCountReadback.restrict model A installed _ child hRead hChildHeaders hChildCells
  have hBitHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 2 (word.bits.map Scalar.bit) ∈ full.headers :=
    hHeaders _ (hChildHeaders _ (List.mem_singleton_self _))
  have hPacked := packed_work model S A layoutStart start plan full loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) word hChildRead hBitHeader rfl
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 0 0 _ installed.root child.root.reference
    (by decide) (Nat.two_pow_pos A) hPointer
  rw [(GeneralPaperStoredBooleanWordSourceRead.source model S A start installed full ctx.contract word hRead hHeaders hRoot).2]
  unfold bound
  dsimp only [loaded,child] at hPacked
  omega

end Blotto.GeneralPaperStoredBooleanWordWork
