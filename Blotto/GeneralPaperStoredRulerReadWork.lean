import Blotto.GeneralPaperStoredFreshWork

/-! The actual ruler reader has two stored reference reads and bounded
control cost. Its measured owner derives the loaded fresh-bit count's fit;
this applies after the same memory is extended by outer fields. -/
namespace Blotto.GeneralPaperStoredRulerReadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperReferenceRegionSlots (Header)
open GeneralPaperUnifiedFieldValue (referenceMemory)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def bound (model : RationalCostModel) (A : ℕ) : ℕ :=
  2 * GeneralPaperStoredReferenceReadWork.readBound model A A + 384 * (A + 1)

theorem work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference) :
    prepared.rangeBits < 2 ^ A ∧ (GeneralPaperStoredRulerRead.read model A installed).2 ≤ bound model A := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hRoot ⟨2,by decide⟩
  let child := GeneralPaperBooleanRecordCursor.child model S A cache .ruler fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  let header : Header A := ⟨child.root,0,[FixedBinaryWord.ofNat A cache.ruler.length]⟩
  have hMember : header ∈ child.headers := List.mem_singleton_self _
  have hOwner := GeneralPaperStoredReadContext.header_capacity ctx header (hHeaders _ (hChildHeaders _ hMember))
  have hCount : cache.ruler.length < 2 ^ A := by
    change fieldStart + A * (2 * cache.ruler.length + 32) < 2 ^ A at hOwner
    have hA := ctx.positive
    nlinarith only [hA,hOwner]
  have hRawPointer := hChildRead.1 header hMember ⟨0,by change 0 < 1; decide⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) loaded.root 0 0).1 =
    some (⟨A,FixedBinaryWord.ofNat A cache.ruler.length⟩ : GeneralPaperMixedReferenceMemory.Word) at hRawPointer
  have hRawBound := GeneralPaperStoredReferenceReadWork.read_work model A A 0 0 _ loaded.root _
    (by decide) (Nat.two_pow_pos A) hRawPointer
  have hLoadBound := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 64 plan full installed ctx
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hHeaders hRoot ⟨2,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 2).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 2).2 ≤ _ at hLoadBound
  have hRawPointerLoaded : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory loaded.memory) loaded.root 0 0).1 =
    some (⟨A,FixedBinaryWord.ofNat A cache.ruler.length⟩ : GeneralPaperMixedReferenceMemory.Word) := hRawPointer
  have hRawWork : (GeneralPaperRulerFieldCursor.read model A loaded).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) loaded.root 0 0).2 + 65 * A + 64 := by
    simp only [GeneralPaperRulerFieldCursor.read,hRawPointerLoaded,Option.elim_some]
    rw [show loaded.memory = installed.memory from rfl]
    ring
  refine ⟨by simpa only [cache.ruler_length] using hCount,?_⟩
  rw [(GeneralPaperStoredRulerRead.trace model A installed loaded hLoad).2,hRawWork]
  unfold bound
  omega

theorem fresh_work {S₀ : Type*} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference)
    (next : S₀ → Bool × S₀) (state : S₀) :
    (GeneralPaperStoredFreshRead.read model A installed next state).work ≤
      bound model A + GeneralPaperStoredFreshWork.bound model A prepared.rangeBits 0 + 128 * (A + 1) := by
  obtain ⟨hFits,hRuler⟩ := work model S A layoutStart start plan full installed ctx cache hRead hHeaders hRoot
  obtain ⟨_,hCount,_⟩ := GeneralPaperStoredRulerRead.source model S A layoutStart start installed full plan ctx.contract ctx.safe ctx.positive ctx.capacity
    cache hRead hHeaders hRoot
  exact (GeneralPaperStoredFreshWork.read_work model A prepared.rangeBits installed next state hCount hFits).trans
    (Nat.add_le_add_right (Nat.add_le_add_right hRuler _) _)

end Blotto.GeneralPaperStoredRulerReadWork
