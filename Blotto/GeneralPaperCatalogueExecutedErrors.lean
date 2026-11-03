import Blotto.GeneralPaperCatalogueTrueScore
import Blotto.GeneralPaperNativeLossErrors

/-! The actual four-family integer increments approximate the exact losses
of the incoming full laws reweighted by the executed epoch history. CDF and
tail errors come from the actual native queries. The chosen row in each
signed loss is the same whole row used by all eight delta arrays.
-/
namespace Blotto.GeneralPaperCatalogueExecutedErrors
open scoped BigOperators
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochMetadata GeneralPaperCatalogueIncoming GeneralPaperCatalogueTrueScore
open GeneralPaperCatalogueQueryErrors GeneralPaperGeometricLevels
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

def unsignedLearner (response : Bool) : Learner := if response then .q else .p

def opponentLearner (response : Bool) : Learner := if response then .p else .q

noncomputable def cdf {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (incoming : Incoming cache) (count : ℕ) (j : Fin m) (cut : ℕ) : ℝ :=
  GeneralPaperCatalogueEpochCDF.currentCDF learner cache Qv weights Bc Br (incoming.mass learner j) count j cut

def counts {m k : ℕ} {cache : Cache m k} (response : Bool) (run : Run cache) (time : ℕ) (j : Fin m) (code : ℕ) :
    GeneralPaperQueryLossCounts.Counts :=
  GeneralPaperNativeLossReference.reference k (8*cache.alphabet.C)
    (summary (opponentLearner response) cache j) (summary (signedLearner response) cache j)
    (block (opponentLearner response) (snapshotAt run time j)).cdf (block (signedLearner response) (snapshotAt run time j)).cdf code

noncomputable def unsignedLoss {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (incoming : Incoming cache) (count : ℕ) (j : Fin m) (code : ℕ) : ℝ :=
  GeneralPaperNativeLossErrors.trueLoss response
    (cdf (opponentLearner response) cache Qv weights Bc Br incoming count j code)
    (cdf (opponentLearner response) cache Qv weights Bc Br incoming count j (code+1))
    (cdf (signedLearner response) cache Qv weights Bc Br incoming count j (8*cache.alphabet.C)-
      cdf (signedLearner response) cache Qv weights Bc Br incoming count j code)
    (cdf (signedLearner response) cache Qv weights Bc Br incoming count j (2*(8*cache.alphabet.C))-
      cdf (signedLearner response) cache Qv weights Bc Br incoming count j (8*cache.alphabet.C+code))

noncomputable def signedLoss {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (incoming : Incoming cache) (count : ℕ) (j : Fin m) (code : ℕ) : ℝ :=
  let projected := GeneralPaperSignedUpdatePlan.project (8*cache.alphabet.C) code
  let trueCDF := cdf (unsignedLearner response) cache Qv weights Bc Br incoming count j (projected+1)
  let positive := decide (code<8*cache.alphabet.C)
  let hit := decide ((chosenCodes response (selected cache Qv weights Bc Br) count).read j≤projected)
  if positive then (if hit then 1 else 0)-trueCDF else trueCDF-(if hit then 1 else 0)

theorem unsigned_increment {m k : ℕ} {cache : Cache m k} (response : Bool) (run : Run cache) (time : ℕ) (j : Fin m) (code : ℕ) :
    increment (unsignedLearner response) run time j code=GeneralPaperQueryLossCounts.increment k response (counts response run time j code) := by
  cases response <;> dsimp only [unsignedLearner,opponentLearner,signedLearner,increment,counts]
  · unfold GeneralPaperEpochDeltaSemantics.pIncrement
    rw [field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl
  · unfold GeneralPaperEpochDeltaSemantics.qIncrement
    rw [field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl

theorem signed_increment {m k : ℕ} {cache : Cache m k} (response : Bool) (run : Run cache) (time : ℕ) (j : Fin m) (code : ℕ) :
    increment (signedLearner response) run time j code=
      GeneralPaperSignedUpdateReference.increment k (8*cache.alphabet.C) ((chosenCodes response run time).read j)
        (summary (unsignedLearner response) cache j) (block (unsignedLearner response) (snapshotAt run time j)).cdf code := by
  cases response <;> dsimp only [signedLearner,unsignedLearner,increment]
  · have hb : (choiceAt run time j).candidateBid=(chosenCodes false run time).read j :=
      GeneralPaperCatalogueEpochRows.field_candidate (rowsAt run time) (stateAt run time) j
    unfold GeneralPaperEpochDeltaSemantics.lambdaIncrement
    rw [hb,field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl
  · have hb : (choiceAt run time j).responseBid=(chosenCodes true run time).read j :=
      GeneralPaperCatalogueEpochRows.field_response (rowsAt run time) (stateAt run time) j
    unfold GeneralPaperEpochDeltaSemantics.muIncrement
    rw [hb,field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl

theorem unsigned_error {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (incoming : Incoming cache) (count : ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (code : ℕ)
    (hCode : code<8*cache.alphabet.C) :
    |unsignedLoss response cache Qv weights Bc Br incoming count j code-
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment (unsignedLearner response)
        (selected cache Qv weights Bc Br) count j code):ℝ)|≤
      25*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+3*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  let run := selected cache Qv weights Bc Br
  let cb := block (opponentLearner response) (snapshotAt run count j)
  let tb := block (signedLearner response) (snapshotAt run count j)
  have cc : cb.cdf=GeneralPaperEpochPrefixArray.build cb.values := block_coherent _ run count j
  have ct : tb.cdf=GeneralPaperEpochPrefixArray.build tb.values := block_coherent _ run count j
  have pc : 0<∑ r, cb.values.read r := block_positive _ cache Qv weights Bc Br count hCount j
  have pt : 0<∑ r, tb.values.read r := block_positive _ cache Qv weights Bc Br count hCount j
  have hBounds : GeneralPaperQueryLossCounts.Bounds k (counts response run count j code) := by
    unfold counts
    rw [cc,ct]
    exact GeneralPaperNativeLossReference.reference_bounds k _ _ _ _ _ pc pt code
  have wc : width (opponentLearner response) cache=8*cache.alphabet.C := by cases response <;> rfl
  have wt : width (signedLearner response) cache=2*(8*cache.alphabet.C) := by cases response <;> rfl
  have hl := cdf_error (opponentLearner response) cache Qv weights Bc Br hOrdered hCodes j _
    (incoming.probability _ j) (incoming.close _ j) count hCount code (by rw [wc]; omega)
  have hh := cdf_error (opponentLearner response) cache Qv weights Bc Br hOrdered hCodes j _
    (incoming.probability _ j) (incoming.close _ j) count hCount (code+1) (by rw [wc]; omega)
  have hp := interval_error (signedLearner response) cache Qv weights Bc Br hOrdered hCodes j _
    (incoming.probability _ j) (incoming.close _ j) count hCount code (8*cache.alphabet.C) hCode.le (by rw [wt]; omega)
  have hn := interval_error (signedLearner response) cache Qv weights Bc Br hOrdered hCodes j _
    (incoming.probability _ j) (incoming.close _ j) count hCount (8*cache.alphabet.C+code) (2*(8*cache.alphabet.C)) (by omega) (by rw [wt])
  rw [unsigned_increment]
  exact GeneralPaperNativeLossErrors.executed_error k response _ hBounds _ _ _ _ hl hh hp hn

theorem signed_error {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (incoming : Incoming cache) (count : ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (code : ℕ)
    (hCode : code<2*(8*cache.alphabet.C)) :
    |signedLoss response cache Qv weights Bc Br incoming count j code-
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment (signedLearner response)
        (selected cache Qv weights Bc Br) count j code):ℝ)|≤
      25*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+3*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  let run := selected cache Qv weights Bc Br
  let b := block (unsignedLearner response) (snapshotAt run count j)
  let s := summary (unsignedLearner response) cache j
  let bid := (chosenCodes response run count).read j
  let projected := GeneralPaperSignedUpdatePlan.project (8*cache.alphabet.C) code
  have hc : b.cdf=GeneralPaperEpochPrefixArray.build b.values := block_coherent _ run count j
  have hp : 0<∑ r, b.values.read r := block_positive _ cache Qv weights Bc Br count hCount j
  have hW : width (unsignedLearner response) cache=8*cache.alphabet.C := by cases response <;> rfl
  have hProjected : projected<8*cache.alphabet.C := GeneralPaperUnsignedPartition.project_bound _ _ hCode
  have hCDF := cdf_error (unsignedLearner response) cache Qv weights Bc Br hOrdered hCodes j _
    (incoming.probability _ j) (incoming.close _ j) count hCount (projected+1) (by rw [hW]; omega)
  have hLoss : executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (increment (signedLearner response) run count j code)=GeneralPaperSignedUpdateReference.loss k (8*cache.alphabet.C) bid s b.cdf code := by
    rw [signed_increment]
    change executedLoss _ (GeneralPaperSignedUpdateReference.increment k _ bid s b.cdf code)=_
    rw [hc]
    exact GeneralPaperSignedUpdateReference.increment_loss k _ bid s b.values hp code
  have hNu : (0:ℝ)≤(GeneralPaperSourceParameters.prepare k).nu := by exact_mod_cast (GeneralPaperSourceParameters.positive k).2.2.1.le
  have hTheta : (0:ℝ)≤(GeneralPaperSourceParameters.prepare k).theta := by exact_mod_cast (GeneralPaperSourceParameters.positive k).2.2.2.le
  rw [hLoss]
  exact GeneralPaperRoundedLosses.signed_error (GeneralPaperSourceParameters.prepare k).meshDenominator
    (GeneralPaperRankedCDFQuery.referenceCount k s b.cdf (projected+1))
    (cdf (unsignedLearner response) cache Qv weights Bc Br incoming count j (projected+1))
    ((GeneralPaperSourceParameters.prepare k).nu:ℝ) ((GeneralPaperSourceParameters.prepare k).theta:ℝ)
    (decide (code<8*cache.alphabet.C)) (decide (bid≤projected)) hNu hTheta hCDF

noncomputable def exactLoss {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (incoming : Incoming cache) (count : ℕ) (j : Fin m) (code : ℕ) : ℝ :=
  match learner with
  | .p => unsignedLoss false cache Qv weights Bc Br incoming count j code
  | .q => unsignedLoss true cache Qv weights Bc Br incoming count j code
  | .lambda => signedLoss false cache Qv weights Bc Br incoming count j code
  | .mu => signedLoss true cache Qv weights Bc Br incoming count j code

theorem error_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (incoming : Incoming cache) (count : ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (code : ℕ)
    (hCode : code<width learner cache) :
    |exactLoss learner cache Qv weights Bc Br incoming count j code-
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta
        (increment learner (selected cache Qv weights Bc Br) count j code):ℝ)|≤49*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/128 := by
  have hConstants := congrArg (fun r : ℚ => (r:ℝ)) (GeneralPaperSourceParameters.loss_error k)
  push_cast at hConstants
  rw [←hConstants]
  cases learner with
  | p => exact unsigned_error false cache Qv weights Bc Br hOrdered hCodes incoming count hCount j code hCode
  | q => exact unsigned_error true cache Qv weights Bc Br hOrdered hCodes incoming count hCount j code hCode
  | lambda => exact signed_error false cache Qv weights Bc Br hOrdered hCodes incoming count hCount j code hCode
  | mu => exact signed_error true cache Qv weights Bc Br hOrdered hCodes incoming count hCount j code hCode

theorem tree_error_bound {m : ℕ} (learner : Learner) (a : GeneralPaperCodeAlphabet.Alphabet) (k : ℕ)
    (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda) (hValid : GeneralPaperCatalogueTreeCache.Valid a k trees)
    (hPaths : GeneralPaperCatalogueTreeCache.Paths a k trees) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (code : ℕ) (hCode : code<2^(GeneralPaperCatalogueTreeCache.treeHeight learner a.lambda)) :
    let cache := GeneralPaperCatalogueTreeCache.prepare (GeneralPaperPreparedPowers.prepare a.lambda k)
      (GeneralPaperQuantileComparison.width a.lambda k) a k trees
    let incoming := fromTrees a k trees hValid hPaths
    |exactLoss learner cache Qv weights Bc Br incoming count j code-
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta
        (increment learner (selected cache Qv weights Bc Br) count j code):ℝ)|≤49*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/128 :=
  error_bound learner _ Qv weights Bc Br (GeneralPaperCatalogueTreeCache.ordered a k trees hValid hPaths)
    (GeneralPaperCatalogueTreeCache.codes_valid _ _ a k trees) _ count hCount j code
    (by rw [GeneralPaperCatalogueTreeCache.width_node]; exact hCode)

end Blotto.GeneralPaperCatalogueExecutedErrors
