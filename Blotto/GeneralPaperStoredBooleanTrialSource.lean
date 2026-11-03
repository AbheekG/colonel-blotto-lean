import Blotto.GeneralPaperStoredBooleanTrial

/-! Actual global ownership discharges every stored-trial refinement premise.
Correct is an erased proposition; the trial accepts only memory/root and its
random-source primitive/state. -/
namespace Blotto.GeneralPaperStoredBooleanTrialSource
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def Correct (model : RationalCostModel) (A : ℕ) (installed : Installed A) (cache : GeneralPaperEqualBooleanCache.Cache prepared) : Prop :=
  (GeneralPaperStoredRulerRead.read model A installed).1 = some prepared.rangeBits ∧
    (GeneralPaperStoredBooleanCacheRead.denominator model A installed).1 = some (⟨prepared.rangeBits + 1,cache.denominator⟩ : Word) ∧
    ∀ word : FixedBinaryWord (prepared.rangeBits + 1),
      (GeneralPaperStoredBooleanCacheRead.categorical model A installed word.bits).1 =
        (GeneralPaperBooleanCategoricalSelect.run cache.rows word).1.map Fin.val

theorem from_directory (model : RationalCostModel) (S A layoutStart start : ℕ) (installed : Installed A)
    (full : Directory A) (plan : GeneralPaperMeasuredBlockPlan.Plan) (hContract : Contract model A installed full)
    (hSafe : GeneralPaperFieldDirectorySafety.Safe (GeneralPaperMeasuredBlockLayout.run model S A layoutStart plan).1 full)
    (hA : 0 < A) (hCap : layoutStart + plan.sizes.sum < 2 ^ A) (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference) :
    Correct model A installed cache := by
  obtain ⟨_,hCount,_⟩ := GeneralPaperStoredRulerRead.source model S A layoutStart start installed full plan hContract hSafe hA hCap cache hRead hHeaders hRoot
  obtain ⟨_,hDenominator,_⟩ := GeneralPaperStoredBooleanCacheRead.denominator_source model S A start installed full hContract cache hRead hHeaders hRoot
  refine ⟨hCount,hDenominator,?_⟩
  intro word
  obtain ⟨_,hCategorical,_⟩ := GeneralPaperStoredBooleanCacheRead.categorical_source model S A start installed full hContract cache hRead hHeaders hRoot word
  exact hCategorical

theorem trial_source (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared) (hCorrect : Correct model A installed cache)
    (bits : Fin (UniformNatRejection.width prepared.D) → Bool) :
    (GeneralPaperStoredBooleanTrial.run model A installed GeneralPaperBooleanFreshWord.nextList
      (List.ofFn (fun i : Fin prepared.rangeBits => bits (i.cast prepared.rangeBits_correct)))).output =
        (GeneralPaperEqualBooleanRejection.trial cache bits).output.map Fin.val ∧
      (GeneralPaperStoredBooleanTrial.run model A installed GeneralPaperBooleanFreshWord.nextList
        (List.ofFn (fun i : Fin prepared.rangeBits => bits (i.cast prepared.rangeBits_correct)))).reads =
          (GeneralPaperEqualBooleanRejection.trial cache bits).reads := by
  have h := GeneralPaperStoredBooleanTrial.source model A installed cache GeneralPaperBooleanFreshWord.nextList
    (List.ofFn (fun i : Fin prepared.rangeBits => bits (i.cast prepared.rangeBits_correct))) hCorrect.1 hCorrect.2.1 hCorrect.2.2
  exact ⟨h.1,h.2.2.1⟩

end Blotto.GeneralPaperStoredBooleanTrialSource
