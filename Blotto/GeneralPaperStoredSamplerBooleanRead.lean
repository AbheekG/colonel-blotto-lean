import Blotto.GeneralPaperStoredBooleanCacheRead

/-! Actual sampler-root descent reaches Boolean words and categorical rows.
The constructor-return theorem joins controls, denominator and the canonical
categorical choice on that very memory, rather than on a source-cache oracle. -/
namespace Blotto.GeneralPaperStoredSamplerBooleanRead
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def denominator (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option Word × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 1
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredBooleanCacheRead.denominator model B loaded
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

def categorical (model : RationalCostModel) (A : ℕ) (installed : Installed A) (bits : List Bool) : Option ℕ × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 1
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredBooleanCacheRead.categorical model B loaded bits
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

theorem denominator_trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : Child)) :
    (denominator model A installed).1 = (GeneralPaperStoredBooleanCacheRead.denominator model A loaded).1 ∧
      (denominator model A installed).2 = (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredBooleanCacheRead.denominator model A loaded).2 + 128 * A + 64 := by
  simp only [denominator,hChild]
  constructor
  · exact True.intro
  · ring

theorem categorical_trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (bits : List Bool)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : Child)) :
    (categorical model A installed bits).1 = (GeneralPaperStoredBooleanCacheRead.categorical model A loaded bits).1 ∧
      (categorical model A installed bits).2 = (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredBooleanCacheRead.categorical model A loaded bits).2 + 128 * A + 64 := by
  simp only [categorical,hChild]
  constructor
  · exact True.intro
  · ring

theorem denominator_source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference) :
    ∃ root : FixedBinaryWord A,
      (denominator model A installed).1 = some (⟨sampler.prepared.rangeBits + 1,sampler.categorical.denominator⟩ : Word) ∧
      (denominator model A installed).2 = (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredBooleanCacheRead.denominator model A (GeneralPaperStoredScalarRead.atRoot installed root)).2 + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields hContract.2.1 hRoot ⟨1,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .boolean fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded (GeneralPaperSamplerRecordCursor.expected model S A sampler start) := hContract
  obtain ⟨_,hv,_⟩ := GeneralPaperStoredBooleanCacheRead.denominator_source model S A fieldStart loaded _ hChildContract
    sampler.categorical hRead hHeaders rfl
  obtain ⟨hData,hWork⟩ := denominator_trace model A installed loaded hLoad
  exact ⟨child.root.reference,hData.trans hv,hWork⟩

theorem categorical_source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (word : FixedBinaryWord (sampler.prepared.rangeBits + 1)) :
    ∃ root : FixedBinaryWord A,
      (categorical model A installed word.bits).1 = (GeneralPaperBooleanCategoricalSelect.run sampler.categorical.rows word).1.map Fin.val ∧
      (categorical model A installed word.bits).2 = (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredBooleanCacheRead.categorical model A (GeneralPaperStoredScalarRead.atRoot installed root) word.bits).2 + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields hContract.2.1 hRoot ⟨1,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .boolean fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded (GeneralPaperSamplerRecordCursor.expected model S A sampler start) := hContract
  obtain ⟨_,hv,_⟩ := GeneralPaperStoredBooleanCacheRead.categorical_source model S A fieldStart loaded _ hChildContract
    sampler.categorical hRead hHeaders rfl word
  obtain ⟨hData,hWork⟩ := categorical_trace model A installed loaded word.bits hLoad
  exact ⟨child.root.reference,hData.trans hv,hWork⟩

theorem every_returned_selection (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned)
    (word : FixedBinaryWord (sampler.prepared.rangeBits + 1)) (rank : Fin sampler.prepared.D) (hValue : word.value = rank.val) :
    (GeneralPaperStoredSamplerControls.read model sampler.address returned).values = some [sampler.exponent,sampler.address] ∧
      (denominator model sampler.address returned).1 = some (⟨sampler.prepared.rangeBits + 1,sampler.categorical.denominator⟩ : Word) ∧
      (categorical model sampler.address returned word.bits).1 = some (GeneralPaperEqualPreparedCache.select sampler.prepared rank).val := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  obtain ⟨_,hControls,_,_⟩ := GeneralPaperStoredSamplerControls.source model S sampler.address 0 returned sampler hContract hRoot
  obtain ⟨_,hDenominator,_⟩ := denominator_source model S sampler.address 0 returned sampler hContract hRoot
  obtain ⟨_,hCategorical,_⟩ := categorical_source model S sampler.address 0 returned sampler hContract hRoot word
  rw [GeneralPaperEqualBooleanCache.selection_data sampler.categorical word rank hValue,Option.map_some] at hCategorical
  exact ⟨hControls,hDenominator,hCategorical⟩

end Blotto.GeneralPaperStoredSamplerBooleanRead
