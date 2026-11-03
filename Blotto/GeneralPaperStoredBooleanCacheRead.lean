import Blotto.GeneralPaperStoredCategoricalScan

/-! The Boolean-cache root exposes its actual denominator word and its
stored-row categorical selector. Neither call receives a source cache. -/
namespace Blotto.GeneralPaperStoredBooleanCacheRead
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def denominator (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option Word × ℕ :=
  GeneralPaperStoredRecordCollectors.word model A installed 0

def categorical (model : RationalCostModel) (A : ℕ) (installed : Installed A) (bits : List Bool) : Option ℕ × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 1
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredCategoricalScan.run model B loaded bits
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

theorem categorical_trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (bits : List Bool)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : Child)) :
    (categorical model A installed bits).1 = (GeneralPaperStoredCategoricalScan.run model A loaded bits).1 ∧
      (categorical model A installed bits).2 = (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredCategoricalScan.run model A loaded bits).2 + 128 * A + 64 := by
  simp only [categorical,hChild]
  constructor
  · exact True.intro
  · ring

theorem denominator_source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference) :
    ∃ root : FixedBinaryWord A,
      (denominator model A installed).1 = some (⟨prepared.rangeBits + 1,cache.denominator⟩ : Word) ∧
      (denominator model A installed).2 = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredBooleanWordRead.read model A (GeneralPaperStoredScalarRead.atRoot installed root)).2 + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hRoot ⟨0,by decide⟩
  let child := GeneralPaperBooleanRecordCursor.child model S A cache .denominator fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded full := hContract
  have hv := (GeneralPaperStoredBooleanWordSourceRead.source model S A fieldStart loaded full hChildContract cache.denominator
    hChildRead (fun header hh => hHeaders header (hChildHeaders header hh)) rfl).1
  obtain ⟨hData,hWork⟩ := GeneralPaperStoredRecordCollectors.word_trace model A installed loaded 0 hLoad
  exact ⟨child.root.reference,hData.trans hv,hWork⟩

theorem categorical_source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference)
    (word : FixedBinaryWord (prepared.rangeBits + 1)) :
    ∃ root : FixedBinaryWord A,
      (categorical model A installed word.bits).1 = (GeneralPaperBooleanCategoricalSelect.run cache.rows word).1.map Fin.val ∧
      (categorical model A installed word.bits).2 = (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredCategoricalScan.run model A (GeneralPaperStoredScalarRead.atRoot installed root) word.bits).2 + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperBooleanRecordCursor.schema model S A cache) (GeneralPaperBooleanRecordCursor.child model S A cache)
    GeneralPaperBooleanRecordCursor.fields hRead hRoot ⟨1,by decide⟩
  let child := GeneralPaperBooleanRecordCursor.child model S A cache .rows fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded full := hContract
  have hv := (GeneralPaperStoredCategoricalScan.source model S A fieldStart loaded full hChildContract cache.rows
    hChildRead (fun header hh => hHeaders header (hChildHeaders header hh)) rfl word).1
  obtain ⟨hData,hWork⟩ := categorical_trace model A installed loaded word.bits hLoad
  exact ⟨child.root.reference,hData.trans hv,hWork⟩

end Blotto.GeneralPaperStoredBooleanCacheRead
