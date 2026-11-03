import Blotto.GeneralPaperCatalogueIncoming

/-! Exact signed-tail objectives of the incoming full laws after the actual
local updates. The two native optimizers satisfy the paper's beta_opt bound
on their own snapshots. Rounded values have total mass one, so the error has
no factor for the number of fields. The tree specialization derives every
incoming CDF certificate and ordered-summary requirement from sparse nodes.
-/
namespace Blotto.GeneralPaperCatalogueTrueScore
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperResponseTag
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochMetadata GeneralPaperCatalogueIncoming GeneralPaperCatalogueRowSemantics
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

def signedLearner (response : Bool) : Learner := if response then .mu else .lambda

def chosenCodes {m k : ℕ} {cache : Cache m k} (response : Bool) (run : Run cache) (time : ℕ) : FixedArrayTable m ℕ :=
  if response then rowCodes cache.response.data (rowsAt run time).response else rowCodes cache.candidate.data (rowsAt run time).candidate

noncomputable def trueScore {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (incoming : Incoming cache) (count : ℕ) (codes : FixedArrayTable m ℕ) : ℝ :=
  ∑ j, (weights.read j:ℝ)/Qv*GeneralPaperCatalogueQueryErrors.signedTail (signedLearner response) cache Qv weights Bc Br
    (incoming.mass (signedLearner response) j) count j (8*cache.alphabet.C) (codes.read j)

noncomputable def roundedValue {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (j : Fin m) (code : ℕ) : ℝ :=
  (GeneralPaperSignedTailProperties.signedValue k (8*cache.alphabet.C) (summary (signedLearner response) cache j)
    (block (signedLearner response) (snapshotAt (selected cache Qv weights Bc Br) count j)).cdf code:ℝ)

noncomputable def roundedScore {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (codes : FixedArrayTable m ℕ) : ℝ :=
  ∑ j, (weights.read j:ℝ)/Qv*roundedValue response cache Qv weights Bc Br count j (codes.read j)

theorem chosen_bound {m k : ℕ} {cache : Cache m k} (response : Bool) (run : Run cache) (time : ℕ) (j : Fin m) :
    (chosenCodes response run time).read j<8*cache.alphabet.C := by
  cases response with
  | false =>
    change (rowCodes cache.candidate.data (rowsAt run time).candidate).read j<_
    rw [rowCodes,FixedArrayTable.read_ofFn]
    have he : cache.candidate.data=GeneralPaperCatalogueArrays.prepare cache.alphabet false k cache.lambda := by
      rw [cache.candidate_spec]; rfl
    rw [he]
    exact GeneralPaperCatalogueArrays.code_bound cache.alphabet false k cache.lambda j _
  | true =>
    change (rowCodes cache.response.data (rowsAt run time).response).read j<_
    rw [rowCodes,FixedArrayTable.read_ofFn]
    have he : cache.response.data=GeneralPaperCatalogueArrays.prepare cache.alphabet true k cache.mu := by
      rw [cache.response_spec]; rfl
    rw [he]
    exact GeneralPaperCatalogueArrays.code_bound cache.alphabet true k cache.mu j _

theorem weighted_error {m : ℕ} (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (x y : Fin m → ℝ) (error : ℝ) (hError : ∀ j, |x j-y j|≤error) :
    |(∑ j, (weights.read j:ℝ)/Qv*x j)-(∑ j, (weights.read j:ℝ)/Qv*y j)|≤error := by
  have hQ : (Qv:ℝ)≠0 := by exact_mod_cast hQv.ne'
  have hSum : (∑ j, (weights.read j:ℝ)/Qv)=1 := by
    rw [←Finset.sum_div]
    have he : (∑ j, (weights.read j:ℝ))=(Qv:ℝ) := by exact_mod_cast hWeights
    rw [he,div_self hQ]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |(weights.read j:ℝ)/Qv*x j-(weights.read j:ℝ)/Qv*y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (weights.read j:ℝ)/Qv*error := by
      apply Finset.sum_le_sum
      intro j _
      rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(weights.read j:ℝ)/Qv)]
      exact mul_le_mul_of_nonneg_left (hError j) (by positivity)
    _ = _ := by rw [←Finset.sum_mul,hSum,one_mul]

theorem score_error {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (hOrdered : Ordered cache) (hCodes : CodesValid cache) (Bc Br : ℚ)
    (incoming : Incoming cache) (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (codes : FixedArrayTable m ℕ) (hBids : ∀ j, codes.read j<8*cache.alphabet.C) :
    |trueScore response cache Qv weights Bc Br incoming count codes-roundedScore response cache Qv weights Bc Br count codes|≤
      20*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+2*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  unfold trueScore roundedScore
  apply weighted_error Qv hQv weights hWeights
  intro j
  exact GeneralPaperCatalogueQueryErrors.signed_tail_error (signedLearner response) cache Qv weights Bc Br hOrdered hCodes j
    (incoming.mass _ j) (incoming.probability _ j) (incoming.close _ j) count hCount (8*cache.alphabet.C) (codes.read j)
    (by cases response <;> rfl) (hBids j).le

theorem rounded_optimality {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (hOrdered : Ordered cache) (hCodes : CodesValid cache) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode cache.alphabet response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget (if response then Br else Bc)) :
    roundedScore response cache Qv weights Bc Br count codes-
      roundedScore response cache Qv weights Bc Br count (chosenCodes response (selected cache Qv weights Bc Br) count)≤
        ((GeneralPaperSourceParameters.prepare k).eta:ℝ)/2 := by
  cases response with
  | false =>
    have he := GeneralPaperCatalogueSnapshotScore.executed_candidate_score cache Qv hQv weights hWeights hOrdered hCodes Bc Br
      count hCount codes choices hDecode hBudget
    have hr := (Rat.cast_le (K:=ℝ)).mpr he
    simpa only [roundedScore,roundedValue,signedLearner,chosenCodes,referenceScore,summary,block,FixedArrayTable.read_ofFn,
      Bool.false_eq_true,ite_false,Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using hr
  | true =>
    have he := GeneralPaperCatalogueSnapshotScore.executed_response_score cache Qv hQv weights hWeights hOrdered hCodes Bc Br
      count hCount codes choices hDecode hBudget
    have hr := (Rat.cast_le (K:=ℝ)).mpr he
    simpa only [roundedScore,roundedValue,signedLearner,chosenCodes,referenceScore,summary,block,FixedArrayTable.read_ofFn,
      ite_true,Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using hr

theorem true_optimality {m k : ℕ} (response : Bool) (cache : Cache m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (hOrdered : Ordered cache) (hCodes : CodesValid cache) (Bc Br : ℚ)
    (incoming : Incoming cache) (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode cache.alphabet response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget (if response then Br else Bc)) :
    trueScore response cache Qv weights Bc Br incoming count codes-
      trueScore response cache Qv weights Bc Br incoming count (chosenCodes response (selected cache Qv weights Bc Br) count)≤
        25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16 := by
  have hNative := rounded_optimality response cache Qv hQv weights hWeights hOrdered hCodes Bc Br count hCount codes choices hDecode hBudget
  have hBids : ∀ j, codes.read j<8*cache.alphabet.C := fun j => valid_in_alphabet cache.alphabet response _
    (GeneralPaperCodeDecodeSound.decode_valid cache.alphabet response _ _ (hDecode j))
  have hComp := abs_le.mp (score_error response cache Qv hQv weights hWeights hOrdered hCodes Bc Br incoming count hCount codes hBids)
  have hOut := abs_le.mp (score_error response cache Qv hQv weights hWeights hOrdered hCodes Bc Br incoming count hCount
    (chosenCodes response (selected cache Qv weights Bc Br) count) (chosen_bound response _ count))
  have hEta : (0:ℝ)<(GeneralPaperSourceParameters.prepare k).eta := by exact_mod_cast (GeneralPaperSourceParameters.positive k).2.1
  have hBeta := congrArg (fun r : ℚ => (r:ℝ)) (GeneralPaperSourceParameters.optimizer_error k)
  push_cast at hBeta
  linarith only [hNative,hComp.2,hOut.1,hEta,hBeta]

theorem tree_optimality {m : ℕ} (response : Bool) (a : Alphabet) (k : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hValid : GeneralPaperCatalogueTreeCache.Valid a k trees) (hPaths : GeneralPaperCatalogueTreeCache.Paths a k trees)
    (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode a response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget (if response then Br else Bc)) :
    let cache := GeneralPaperCatalogueTreeCache.prepare (GeneralPaperPreparedPowers.prepare a.lambda k)
      (GeneralPaperQuantileComparison.width a.lambda k) a k trees
    let incoming := fromTrees a k trees hValid hPaths
    trueScore response cache Qv weights Bc Br incoming count codes-
      trueScore response cache Qv weights Bc Br incoming count (chosenCodes response (selected cache Qv weights Bc Br) count)≤
        25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16 :=
  true_optimality response _ Qv hQv weights hWeights (GeneralPaperCatalogueTreeCache.ordered a k trees hValid hPaths)
    (GeneralPaperCatalogueTreeCache.codes_valid _ _ a k trees) Bc Br _ count hCount codes choices hDecode hBudget

end Blotto.GeneralPaperCatalogueTrueScore
