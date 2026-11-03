import Blotto.GeneralPaperStoredPreparedGroups

/-! The actual sampler-root postselection computation produces a midpoint
from loaded controls and materializes the selected scaled group vector from
loaded endpoints and budget. It receives no source-cache emission callback. -/
namespace Blotto.GeneralPaperStoredSamplerGroups
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) (midpoint : ℚ) : Option (Array ℚ) × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 0
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredPreparedGroups.run model B loaded index midpoint
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

def draw {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ)
    (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result (Array ℚ) S :=
  let midpoint := GeneralPaperStoredSamplerMidpoint.run model A installed next state
  match midpoint.output with
  | none => ⟨none,midpoint.state,midpoint.reads,midpoint.work + 64 * (A + 1)⟩
  | some value =>
    let groups := run model A installed index value
    ⟨groups.1,midpoint.state,midpoint.reads,midpoint.work + groups.2 + 128 * (A + 1)⟩

theorem trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (index : ℕ) (midpoint : ℚ)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child)) :
    (run model A installed index midpoint).1 = (GeneralPaperStoredPreparedGroups.run model A loaded index midpoint).1 ∧
      (run model A installed index midpoint).2 = (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredPreparedGroups.run model A loaded index midpoint).2 + 128 * A + 64 := by
  simp only [run,hChild]
  constructor
  · exact True.intro
  · ring

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    ∃ root : FixedBinaryWord A,
      (run model A installed index.val (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh)).1 =
        some (GeneralPaperEqualCachedEmission.scaledPoint sampler.prepared index fresh).data ∧
      (run model A installed index.val (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh)).2 =
        (GeneralPaperStoredChildRead.load model A installed 0 0).2 +
        (GeneralPaperStoredPreparedGroups.run model A (GeneralPaperStoredScalarRead.atRoot installed root) index.val
          (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh)).2 + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields hContract.2.1 hRoot ⟨0,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .prepared fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded (GeneralPaperSamplerRecordCursor.expected model S A sampler start) := hContract
  obtain ⟨_,hv,_⟩ := GeneralPaperStoredPreparedGroups.source model S A fieldStart loaded _ hChildContract sampler.prepared hRead hHeaders rfl index fresh
  obtain ⟨hData,hWork⟩ := trace model A installed loaded index.val (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh) hLoad
  exact ⟨child.root.reference,hData.trans hv,hWork⟩

theorem draw_source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (draw model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
      some (GeneralPaperEqualCachedEmission.scaledPoint sampler.prepared index fresh).data ∧
      (draw model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (draw model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = sampler.prepared.midpointBits ∧
      (draw model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work =
        (GeneralPaperStoredSamplerMidpoint.run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work +
        (run model A installed index.val (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh)).2 + 128 * (A + 1) := by
  obtain ⟨_,hMidpoint,hState,hReads,_⟩ := GeneralPaperStoredSamplerMidpoint.source model S A start installed sampler hContract hRoot fresh
  obtain ⟨_,hGroups,_⟩ := source model S A start installed sampler hContract hRoot index fresh
  simp only [draw,hMidpoint,hState,hReads,hGroups,and_self]

theorem every_returned_draw (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (draw model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
      some (GeneralPaperEqualCachedEmission.scaledPoint sampler.prepared index fresh).data ∧
      (draw model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (draw model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = sampler.prepared.midpointBits ∧
      (draw model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work =
        (GeneralPaperStoredSamplerMidpoint.run model sampler.address returned GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work +
        (run model sampler.address returned index.val (GeneralPaperEqualPreparedCache.midpoint sampler.prepared fresh)).2 + 128 * (sampler.address + 1) := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact draw_source model S sampler.address 0 returned sampler hContract hRoot index fresh

end Blotto.GeneralPaperStoredSamplerGroups
