import Blotto.GeneralPaperStoredMidpointRead

/-! The actual sampler root loads its prepared child before midpoint
production. One actual constructor return supplies all controls, fresh-bit
length, midpoint count and read/copy/arithmetic work in that same memory. -/
namespace Blotto.GeneralPaperStoredSamplerMidpoint
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result ℚ S :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 0
  match child.1 with
  | none => ⟨none,state,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredMidpointRead.run model B loaded next state
    ⟨actual.output,actual.state,actual.reads,child.2 + actual.work + 64 * (A + B + 1)⟩

theorem trace {S : Type*} (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A)
    (next : S → Bool × S) (state : S)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child)) :
    (run model A installed next state).output = (GeneralPaperStoredMidpointRead.run model A loaded next state).output ∧
      (run model A installed next state).state = (GeneralPaperStoredMidpointRead.run model A loaded next state).state ∧
      (run model A installed next state).reads = (GeneralPaperStoredMidpointRead.run model A loaded next state).reads ∧
      (run model A installed next state).work = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredMidpointRead.run model A loaded next state).work + 128 * A + 64 := by
  simp only [run,hChild]
  refine ⟨True.intro,True.intro,True.intro,?_⟩
  ring

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (fresh : Fin sampler.prepared.midpointBits → Bool) :
    ∃ root : FixedBinaryWord A,
      (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
        some (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh) ∧
      (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = sampler.prepared.midpointBits ∧
      (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work =
        (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredMidpointRead.run model A (GeneralPaperStoredScalarRead.atRoot installed root)
          GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields hContract.2.1 hRoot ⟨0,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .prepared fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded (GeneralPaperSamplerRecordCursor.expected model S A sampler start) := hContract
  obtain ⟨hv,hs,hr,_⟩ := GeneralPaperStoredMidpointRead.source model S A fieldStart loaded _ hChildContract sampler.prepared hRead hHeaders rfl fresh
  obtain ⟨hData,hState,hReads,hWork⟩ := trace model A installed loaded GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh) hLoad
  exact ⟨child.root.reference,hData.trans hv,hState.trans hs,hReads.trans hr,hWork⟩

theorem every_returned (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned)
    (fresh : Fin sampler.prepared.midpointBits → Bool) :
    ∃ root : FixedBinaryWord sampler.address,
      (run model sampler.address returned GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
        some (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh) ∧
      (run model sampler.address returned GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (run model sampler.address returned GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = sampler.prepared.midpointBits ∧
      (run model sampler.address returned GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work =
        (GeneralPaperStoredChildRead.load model sampler.address returned 0 0).2 +
        (GeneralPaperStoredMidpointRead.run model sampler.address (GeneralPaperStoredScalarRead.atRoot returned root)
          GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work + 128 * sampler.address + 64 := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact source model S sampler.address 0 returned sampler hContract hRoot fresh

end Blotto.GeneralPaperStoredSamplerMidpoint
