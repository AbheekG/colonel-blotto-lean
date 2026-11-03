import Blotto.GeneralPaperCatalogueCellHistory

/-! Finite-horizon analysis extensions of the actual epoch increments.
Local increments are zero after the epoch; this is constant executed loss
-2 and changes no normalized law. Splicing retains every preceding global
increment. No runtime restart or reset of the full learner is performed.
-/
namespace Blotto.GeneralPaperCatalogueHorizon
open scoped BigOperators
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochMetadata GeneralPaperCatalogueLossBounds
open GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

def finiteIncrement {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (i : Fin (width learner cache)) : ℕ :=
  if time<(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period then
    increment learner (selected cache Qv weights Bc Br) time j i.val else 0

theorem finite_eq {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (hTime : time<(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (i : Fin (width learner cache)) :
    finiteIncrement learner cache Qv weights Bc Br time j i=increment learner (selected cache Qv weights Bc Br) time j i.val := by
  simp only [finiteIncrement,hTime,ite_true]

theorem finite_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (i : Fin (width learner cache)) :
    finiteIncrement learner cache Qv weights Bc Br time j i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  dsimp only [finiteIncrement]
  split
  · rename_i ht
    exact increment_bound learner cache Qv weights Bc Br time ht.le j i.val
  · exact Nat.zero_le _

theorem finite_magnitude {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (i : Fin (width learner cache)) :
    |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (finiteIncrement learner cache Qv weights Bc Br time j i):ℝ)|≤2 := by
  dsimp only [finiteIncrement]
  split
  · rename_i ht
    exact magnitude_bound learner cache Qv weights Bc Br time ht.le j i.val
  · norm_num [executedLoss]

theorem variation_code {n : ℕ} (hn : 0<n) (f : ℕ → ℝ) :
    variation (fun i => f (code hn i).val) (n-1)=variation f (n-1) := by
  unfold variation
  apply Finset.sum_congr rfl
  intro i hi
  have hI := Finset.mem_range.mp hi
  have hc : (code hn i).val=i := by dsimp only [code]; omega
  have hs : (code hn (i+1)).val=i+1 := by dsimp only [code]; omega
  dsimp only
  rw [hc,hs]

theorem finite_variation {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (time : ℕ) (j : Fin m) :
    variation (fun i => (executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (finiteIncrement learner cache Qv weights Bc Br time j (code (width_positive learner cache) i)):ℝ)) (width learner cache-1)≤4 := by
  by_cases ht : time<(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period
  · simp only [finiteIncrement,ht,ite_true]
    rw [variation_code (width_positive learner cache)
      (fun i => (executedLoss (GeneralPaperSourceParameters.prepare k).theta
        (increment learner (selected cache Qv weights Bc Br) time j i):ℝ))]
    exact variation_bound learner cache Qv weights Bc Br hOrdered hCodes time ht.le j
  · simp [finiteIncrement,ht,variation]

def location {m k : ℕ} (learner : Learner) (cache : Cache m k) (hCodes : CodesValid cache) (j : Fin m)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) : Fin (width learner cache) :=
  ⟨(summary learner cache j).read r,hCodes learner j r⟩

theorem occurrence_finite {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hCodes : CodesValid cache) (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (time : ℕ) (hTime : time<count) (j : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (occurrenceDelta learner (deltaAt (selected cache Qv weights Bc Br) time j)).read r=
      finiteIncrement learner cache Qv weights Bc Br time j (location learner cache hCodes j r) := by
  rw [finite_eq learner cache Qv weights Bc Br time (by omega)]
  exact delta_read learner _ time j r

def continuation {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (past : ℕ → Fin (width learner cache) → ℕ) (start time : ℕ) (j : Fin m) (i : Fin (width learner cache)) : ℕ :=
  if time<start then past time i else finiteIncrement learner cache Qv weights Bc Br (time-start) j i

theorem continuation_local {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (past : ℕ → Fin (width learner cache) → ℕ) (start time : ℕ) (j : Fin m) (i : Fin (width learner cache)) :
    continuation learner cache Qv weights Bc Br past start (start+time) j i=finiteIncrement learner cache Qv weights Bc Br time j i := by
  simp only [continuation,show ¬start+time<start by omega,ite_false,Nat.add_sub_cancel_left]

theorem continuation_levels {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (past : ℕ → Fin (width learner cache) → ℕ) (start : ℕ) (j : Fin m) (i : Fin (width learner cache)) :
    levels (fun t => continuation learner cache Qv weights Bc Br past start t j) start i=levels past start i := by
  apply GeneralPaperEpochLevelArray.levels_agree
  intro t ht
  simp only [continuation,ht,ite_true]

theorem continuation_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (past : ℕ → Fin (width learner cache) → ℕ) (start : ℕ)
    (hPast : ∀ t<start, ∀ i, past t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) (time : ℕ) (j : Fin m) (i : Fin (width learner cache)) :
    continuation learner cache Qv weights Bc Br past start time j i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  dsimp only [continuation]
  split
  · rename_i ht
    exact hPast time ht i
  · exact finite_bound learner cache Qv weights Bc Br _ j i

theorem continuation_magnitude {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (past : ℕ → Fin (width learner cache) → ℕ) (start : ℕ)
    (hPast : ∀ t<start, ∀ i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (past t i):ℝ)|≤2)
    (time : ℕ) (j : Fin m) (i : Fin (width learner cache)) :
    |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (continuation learner cache Qv weights Bc Br past start time j i):ℝ)|≤2 := by
  dsimp only [continuation]
  split
  · rename_i ht
    exact hPast time ht i
  · exact finite_magnitude learner cache Qv weights Bc Br _ j i

theorem continuation_variation {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (past : ℕ → Fin (width learner cache) → ℕ) (start : ℕ)
    (hPast : ∀ t<start, variation (fun i => (executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (past t (code (width_positive learner cache) i)):ℝ)) (width learner cache-1)≤4) (time : ℕ) (j : Fin m) :
    variation (fun i => (executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (continuation learner cache Qv weights Bc Br past start time j (code (width_positive learner cache) i)):ℝ)) (width learner cache-1)≤4 := by
  by_cases ht : time<start
  · simp only [continuation,ht,ite_true]
    exact hPast time ht
  · simp only [continuation,ht,ite_false]
    exact finite_variation learner cache Qv weights Bc Br hOrdered hCodes _ j

theorem occurrence_continuation {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hCodes : CodesValid cache) (past : ℕ → Fin (width learner cache) → ℕ) (start count : ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (time : ℕ) (hTime : time<count) (j : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (occurrenceDelta learner (deltaAt (selected cache Qv weights Bc Br) time j)).read r=
      continuation learner cache Qv weights Bc Br past start (start+time) j (location learner cache hCodes j r) := by
  rw [continuation_local]
  exact occurrence_finite learner cache Qv weights Bc Br hCodes count hCount time hTime j r

end Blotto.GeneralPaperCatalogueHorizon
