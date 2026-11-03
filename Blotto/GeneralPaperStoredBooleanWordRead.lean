import Blotto.GeneralPaperStoredReadStreamSources

/-! Boolean words are reconstructed using their loaded bit count. Successful
collector length supplies the erased word-size proof. A record reader first
loads the actual bit-list root, then reconstructs that word in the same memory. -/
namespace Blotto.GeneralPaperStoredBooleanWordRead
open GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def packResult (A : ℕ) (actual : GeneralPaperStoredReadStream.Result Bool)
    (hLength : ∀ values,actual.values = some values → values.length = actual.count) : Option Word × ℕ :=
  match hParsed : actual.values with
  | none => (none,actual.work + 64 * (A + 1))
  | some values =>
    let word : FixedBinaryWord actual.count := ⟨values,hLength values hParsed⟩
    (some ⟨actual.count,word⟩,actual.work + GeneralPaperEncodedScalarStorage.natBits actual.count + 64 * (A + 1))

def packed (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option Word × ℕ :=
  packResult A (GeneralPaperStoredReadStream.bits model A installed) (GeneralPaperStoredReadStream.bits_length model A installed)

theorem pack_result_source {w : ℕ} (A : ℕ) (actual : GeneralPaperStoredReadStream.Result Bool)
    (hLength : ∀ values,actual.values = some values → values.length = actual.count) (source : FixedBinaryWord w)
    (hValues : actual.values = some source.bits) (hCount : actual.count = w) :
    (packResult A actual hLength).1 = some (⟨w,source⟩ : Word) ∧
      (packResult A actual hLength).2 = actual.work + GeneralPaperEncodedScalarStorage.natBits w + 64 * (A + 1) := by
  cases actual with
  | mk values count work =>
    dsimp only at hValues hCount hLength ⊢
    subst count
    cases values with
    | none => cases hValues
    | some values =>
      have he : values = source.bits := Option.some.inj hValues
      subst values
      simp only [packResult]
      exact ⟨True.intro,True.intro⟩

theorem packed_source {w : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (source : FixedBinaryWord w)
    (hValues : (GeneralPaperStoredReadStream.bits model A installed).values = some source.bits)
    (hCount : (GeneralPaperStoredReadStream.bits model A installed).count = w) :
    (packed model A installed).1 = some (⟨w,source⟩ : Word) ∧
      (packed model A installed).2 = (GeneralPaperStoredReadStream.bits model A installed).work +
        GeneralPaperEncodedScalarStorage.natBits w + 64 * (A + 1) :=
  pack_result_source A _ (GeneralPaperStoredReadStream.bits_length model A installed) source hValues hCount

theorem bits_source {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (source : FixedBinaryWord w)
    (hRead : Readback model A installed (GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits))
    (hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A start 32 2 (source.bits.map Scalar.bit) ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits).root.reference) :
    (packed model A installed).1 = some (⟨w,source⟩ : Word) ∧
      (packed model A installed).2 = (GeneralPaperStoredReadStream.bits model A installed).work +
        GeneralPaperEncodedScalarStorage.natBits w + 64 * (A + 1) := by
  obtain ⟨hv,hc,_⟩ := GeneralPaperStoredReadStreamSources.bits model S A start installed full hContract source.bits hRead hHeader hRoot
  exact packed_source model A installed source hv (hc.trans source.size)

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option Word × ℕ :=
  let pointer := GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 0
  match pointer.1 with
  | none => (none,pointer.2 + 64 * (A + 1))
  | some ⟨B,root⟩ =>
    let word := packed model B (GeneralPaperStoredScalarRead.atRoot installed root)
    (word.1,pointer.2 + word.2 + 64 * (A + B + 1))

theorem trace (model : RationalCostModel) (A : ℕ) (installed : Installed A) (root : FixedBinaryWord A) (word : Word)
    (hPointer : (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 0).1 = some (⟨A,root⟩ : Word))
    (hWord : (packed model A (GeneralPaperStoredScalarRead.atRoot installed root)).1 = some word) :
    (read model A installed).1 = some word ∧ (read model A installed).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 0).2 +
      (packed model A (GeneralPaperStoredScalarRead.atRoot installed root)).2 + 128 * A + 64 := by
  simp only [read,hPointer,hWord]
  constructor
  · exact True.intro
  · ring

end Blotto.GeneralPaperStoredBooleanWordRead
