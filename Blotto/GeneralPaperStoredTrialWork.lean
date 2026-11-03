import Blotto.GeneralPaperStoredCacheCategoricalWork

/-! One actual stored rejection trial joins fresh count/word production,
denominator reconstruction, Boolean comparison and categorical selection.
All resource premises come from the same actual enclosing directory context. -/
namespace Blotto.GeneralPaperStoredTrialWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def bound (model : RationalCostModel) (A w r count : ℕ) : ℕ :=
  GeneralPaperStoredRulerReadWork.bound model A + GeneralPaperStoredFreshWork.bound model A w 0 + 128 * (A + 1) +
  GeneralPaperStoredDenominatorWork.bound model A (w + 1) + 22 * (w + 1) + 8 +
  GeneralPaperStoredCacheCategoricalWork.bound model A (w + 1) r count + 128 * (A + 1)

theorem work {S₀ : Type*} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference)
    (next : S₀ → Bool × S₀) (state : S₀) :
    (GeneralPaperStoredBooleanTrial.run model A installed next state).work ≤
      bound model A prepared.rangeBits (GeneralPaperPositiveSegmentCompaction.count l) cache.rows.length := by
  have hCorrect := GeneralPaperStoredBooleanTrialSource.from_directory model S A layoutStart start installed full plan
    ctx.contract ctx.safe ctx.positive ctx.capacity cache hRead hHeaders hRoot
  have hFresh := GeneralPaperStoredRulerReadWork.fresh_work model S A layoutStart start plan full installed ctx cache hRead hHeaders hRoot next state
  have hDenom := GeneralPaperStoredDenominatorWork.work model S A layoutStart start plan full installed ctx cache hRead hHeaders hRoot
  let word := (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1
  have hSelect := GeneralPaperStoredCacheCategoricalWork.work model S A layoutStart start plan full installed ctx cache hRead hHeaders hRoot word
  have hSource := (GeneralPaperStoredBooleanTrial.source model A installed cache next state hCorrect.1 hCorrect.2.1 hCorrect.2.2).2.2.2
  rw [hSource]
  unfold GeneralPaperStoredBooleanTrial.price
  dsimp only
  dsimp only [word] at hSelect
  rw [GeneralPaperBooleanBorrow.subtract_work]
  change _ + _ + (22 * (prepared.rangeBits + 1) + 8) + _ ≤ _
  unfold bound
  split_ifs <;> omega

end Blotto.GeneralPaperStoredTrialWork
