import Blotto.GeneralPaperStoredPreparationWorkRates

/-! Join the complete measured count/installation prices to actual sampler
constructor returns and the outer extension of the same memory. The source
plan and directory cursor are charged once and remain explicit: sharp prices
for those earlier passes are separate remaining obligations. -/
namespace Blotto.GeneralPaperStoredPreparationConstructorWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

theorem sampler_prefix_work (model : RationalCostModel) (S A start : ℕ)
    (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest
    (GeneralPaperCountedSamplerInstallation.run model S A source regions).work ≤
      (GeneralPaperSamplerRecordCursor.run model S A source regions).work +
        GeneralPaperStoredDirectoryPreparationWork.bound model S A (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum := by
  dsimp only
  obtain ⟨hParsed,_,hSafe,hCovered⟩ := GeneralPaperSamplerRecordCursor.success model S A start source rest
  have h := GeneralPaperStoredDirectoryPreparationWork.finish_work model S A start
    (GeneralPaperSamplerRecordCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest)).work
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)
    (GeneralPaperSamplerRecordCursor.expected model S A source start) hSafe hCovered
    (GeneralPaperEqualMeasuredPlanPositive.sampler model S A source hA) hA hCap
  rw [(GeneralPaperCountedSamplerInstallation.on_parsed model S A source _ _ hParsed).2.2]
  exact h

def buildBound (model : RationalCostModel) (S : ℕ)
    (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  let A := source.address
  let plan := GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A 0 plan).1
  plan.work + (plan.sizes.sum + 1) * GeneralPaperSequentialLayout.stepPrice model S A +
    (GeneralPaperSamplerRecordCursor.run model S A source regions).work +
    GeneralPaperStoredDirectoryPreparationWork.bound model S A plan.sizes.sum + 128 * (S + A + 1)

theorem build_work (model : RationalCostModel) (S : ℕ)
    (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address) :
    (GeneralPaperCountedSamplerInstallation.build model S source).work ≤ buildBound model S source := by
  let A := source.address
  let plan := GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A 0 plan).1
  have hPos := GeneralPaperEqualMeasuredPlanPositive.sampler model S A source hA
  have hLayout := GeneralPaperMeasuredBlockLayout.work model S A 0 plan hA (by simpa only [Nat.zero_add] using hCap)
  have hCount := GeneralPaperMeasuredPlanPositive.block_count plan hPos
  have hm := Nat.mul_le_mul_right (GeneralPaperSequentialLayout.stepPrice model S A) (Nat.add_le_add_right hCount 1)
  have hRun := sampler_prefix_work model S A 0 source [] hA (by simpa only [Nat.zero_add] using hCap)
  obtain ⟨inner,hInner,_,hInnerWork,_,_⟩ := GeneralPaperCountedSamplerInstallation.sampler_prefix model S A 0 source [] hA (by simpa only [Nat.zero_add] using hCap)
  simp only [List.append_nil] at hRun hInner hInnerWork
  have hBuilt := (GeneralPaperCountedSamplerInstallation.build_on_return model S source inner hInner).2.2
  change (GeneralPaperCountedSamplerInstallation.build model S source).work =
    (GeneralPaperMeasuredBlockLayout.run model S A 0 plan).2.2 + inner.work + 64 * (S + A + 1) at hBuilt
  change (GeneralPaperCountedSamplerInstallation.run model S A source regions).work ≤
    (GeneralPaperSamplerRecordCursor.run model S A source regions).work +
      GeneralPaperStoredDirectoryPreparationWork.bound model S A plan.sizes.sum at hRun
  change inner.work = (GeneralPaperCountedSamplerInstallation.run model S A source regions).work at hInnerWork
  change _ ≤ plan.work + (plan.sizes.sum + 1) * GeneralPaperSequentialLayout.stepPrice model S A +
    (GeneralPaperSamplerRecordCursor.run model S A source regions).work +
    GeneralPaperStoredDirectoryPreparationWork.bound model S A plan.sizes.sum + 128 * (S + A + 1)
  omega

theorem every_returned_work (model : RationalCostModel) (S : ℕ)
    (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (returned : Installed source.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S source).values = some returned) :
    returned.work ≤ buildBound model S source := by
  obtain ⟨actual,hActual,_,hWork,_,_⟩ := GeneralPaperCountedSamplerInstallation.build_source model S source hA hCap
  have hSame : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hSame,hWork]
  exact build_work model S source hA hCap

def outerBound (model : RationalCostModel) (S I A B : ℕ) : ℕ :=
  2 * GeneralPaperStoredHeaderPreparationWork.encodeBound model S A +
    GeneralPaperStoredDirectoryPreparationWork.installBound model S A B + 128 * (S + I + A + 1)

theorem outer_work (model : RationalCostModel) (S I A start prefixWork tag : ℕ) (inner : Installed I)
    (hA : 0 < A) (hI : I ≤ A) (hTag : tag < 2 ^ A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (GeneralPaperEqualOuterFieldLayout.canonical A start) inner tag).work ≤
      prefixWork + inner.work + outerBound model S I A (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum := by
  let branch := GeneralPaperStoredWordEncoding.word model S A inner.root.value
  let marker := GeneralPaperStoredWordEncoding.word model S A tag
  let directory := GeneralPaperStoredOuterDirectory.directory A (GeneralPaperEqualOuterFieldLayout.canonical A start) branch.1 marker.1
  have hRoot := GeneralPaperStoredReferenceReadWork.fixed_word_width inner.root
  have hEncode := GeneralPaperStoredWordEncoding.work model S A inner.root.value (A + 8) (by omega)
  have hTagWidth := binaryWordWidth_le_of_lt_pow hA hTag
  have hMarker := GeneralPaperStoredWordEncoding.work model S A tag (A + 8) (by omega)
  have hInstall := GeneralPaperStoredDirectoryPreparationWork.extension_work model S A start
    (GeneralPaperEqualMeasuredSelectedPlan.header model S A) directory inner.memory
    (GeneralPaperStoredOuterDirectory.safe model S A start branch.1 marker.1)
    (GeneralPaperStoredOuterDirectory.covered model S A start branch.1 marker.1)
    (GeneralPaperStoredOuterDirectory.positive model S A hA) hA hCap
  change branch.2 ≤ GeneralPaperStoredHeaderPreparationWork.encodeBound model S A at hEncode
  change marker.2 ≤ GeneralPaperStoredHeaderPreparationWork.encodeBound model S A at hMarker
  change prefixWork + inner.work + branch.2 + marker.2 +
    (GeneralPaperStoredDirectoryExtension.install model S A directory inner.memory).work + 128 * (S + I + A + 1) ≤ _
  unfold outerBound
  omega

end Blotto.GeneralPaperStoredPreparationConstructorWork
