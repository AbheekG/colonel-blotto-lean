import Blotto.GeneralPaperUniformResourceGrowth

/-! The actual original-input resource domain. Its source record is derived
from native preparation; original precision and accuracy encoding enter one
additive erased height ledger. No matching condition over arbitrary source
records, encoding census, capacity oracle or additional native pass is used. -/
namespace Blotto.GeneralPaperNativeResourceDomain
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

structure Problem where
  n : ℕ
  values : FixedArrayTable n ℚ
  selector : RationalFieldSelector n
  correct : ∀ j,values.read j=selector.weight j
  words : BinaryAccuracyWords
  budget : ℚ
  budget_valid : 0<budget ∧ budget<1

def exponent (p : Problem) : ℕ := (GeneralPaperBinaryAccuracy.prepare (fun w => w) 1 p.words).1

def originalSize (p : Problem) : ℕ := GeneralPaperValueRoundingInputPrice.inputSize p.values

def accuracySize (p : Problem) : ℕ := 2*(GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words+1)

def originalInputSize (p : Problem) : ℕ := originalSize p+rationalWordWidth p.budget

def ledger (p : Problem) : ℕ := originalInputSize p+accuracySize p+1

theorem budget_height (p : Problem) : RationalHeight p.budget (rationalWordWidth p.budget) := by
  have hn := lt_pow_binaryWordWidth p.budget.num.natAbs
  have hd := lt_pow_binaryWordWidth p.budget.den
  exact ⟨hn.trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by unfold rationalWordWidth;omega)),
    hd.trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by unfold rationalWordWidth;omega))⟩

def source (model : RationalCostModel) (p : Problem) : GeneralPaperSourceWordGrowth.Input :=
  GeneralPaperOriginalSourceValuePreparation.input
    (GeneralPaperNativePreparationReferenceContract.data model (exponent p) p.values p.selector p.correct)
    (exponent p) (ledger p) p.budget p.budget_valid
    ((budget_height p).mono (by unfold ledger originalInputSize;omega))

def logarithm (model : RationalCostModel) (p : Problem) : ℕ := GeneralPaperSourceWordGrowth.logSize (source model p)

theorem logarithm_positive (model : RationalCostModel) (p : Problem) : 1≤logarithm model p :=
  GeneralPaperSourceWordGrowth.size_positive (source model p)

theorem source_count (model : RationalCostModel) (p : Problem) :
    (source model p).m=(GeneralPaperNativePreparationReferenceContract.data model (exponent p) p.values p.selector p.correct).reduced.m := rfl

theorem source_denominator (model : RationalCostModel) (p : Problem) :
    (source model p).Qv=(GeneralPaperNativePreparationReferenceContract.data model (exponent p) p.values p.selector p.correct).Qv := rfl

theorem source_exponent (model : RationalCostModel) (p : Problem) : (source model p).k=exponent p := rfl

theorem native_exponent (W : ℕ) (p : Problem) :
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1=exponent p :=
  GeneralPaperOriginalSourceDataCalibration.exponent_models W p.words

theorem source_height (model : RationalCostModel) (p : Problem) : (source model p).B=originalInputSize p+accuracySize p+1 := rfl

theorem word_below_ledger (model : RationalCostModel) (p : Problem) (z : ℕ) (h : z≤ledger p) :
    binaryWordWidth z≤logarithm model p := by
  have hw := binaryWordWidth_mono (show z≤ledger p+1 by omega)
  have hl : binaryWordWidth (ledger p+1)≤logarithm model p := by
    change binaryWordWidth ((source model p).B+1)≤GeneralPaperSourceWordGrowth.logSize (source model p)
    unfold GeneralPaperSourceWordGrowth.logSize
    omega
  exact hw.trans hl

theorem small_below_ledger (model : RationalCostModel) (f : Problem → ℕ) (h : ∀ p,f p≤ledger p) :
    GeneralPaperUniformResourceGrowth.Small f (logarithm model) := by
  refine ⟨1,?_⟩
  intro p
  simpa only [Nat.one_mul] using word_below_ledger model p (f p) (h p)

theorem original_small (model : RationalCostModel) : GeneralPaperUniformResourceGrowth.Small originalSize (logarithm model) := by
  apply small_below_ledger model
  intro p
  unfold ledger originalInputSize
  omega

theorem accuracy_small (model : RationalCostModel) : GeneralPaperUniformResourceGrowth.Small accuracySize (logarithm model) := by
  apply small_below_ledger model
  intro p
  unfold ledger
  omega

theorem original_input_small (model : RationalCostModel) : GeneralPaperUniformResourceGrowth.Small originalInputSize (logarithm model) := by
  apply small_below_ledger model
  intro p
  unfold ledger
  omega

theorem count_small (model : RationalCostModel) : GeneralPaperUniformResourceGrowth.Small Problem.n (logarithm model) := by
  apply small_below_ledger model
  intro p
  have hn := GeneralPaperOriginalValueBitDriverRate.input_fields p.values
  change p.n≤originalSize p at hn
  unfold ledger originalInputSize
  omega

theorem exponent_tight (model : RationalCostModel) : GeneralPaperUniformResourceGrowth.Tight exponent (logarithm model) :=
  GeneralPaperUniformResourceGrowth.pullback_source_tight GeneralPaperSourceWordGrowth.k_tight (source model)

theorem prior_source_word_tight (model : RationalCostModel) (C d : ℕ) :
    GeneralPaperUniformResourceGrowth.Tight (fun p => GeneralPaperFastDriverReference.width C d (source model p)) (logarithm model) :=
  GeneralPaperUniformResourceGrowth.pullback_source_tight (GeneralPaperFastDriverReference.width_tight C d) (source model)

theorem whole_price_at_one_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    GeneralPaperUniformResourceGrowth.Small (fun p => GeneralPaperFastWholeDriverStorage.price model C d 1
      (source model p).m (source model p).k (source model p).Qv (source model p).B) (logarithm model) :=
  GeneralPaperUniformResourceGrowth.pullback_source_small
    (GeneralPaperOriginalStrategyProfileGrowth.whole_price_small hg (fun _ => 1) (GeneralPaperSourceWordGrowth.tight_constant 1)) (source model)

theorem whole_space_at_one {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    GeneralPaperUniformResourceGrowth.Bound (fun p => GeneralPaperFastWholeDriverStorage.profile model C d 1
      (source model p).m (source model p).k (source model p).Qv (source model p).B)
      (fun p => GeneralPaperFastFrontStorageRates.rate (source model p)) (logarithm model) := by
  apply GeneralPaperUniformResourceGrowth.dominated
    (GeneralPaperUniformResourceGrowth.pullback_source_bound
      (GeneralPaperFastWholeDriverStorageRates.profile_rate C d (fun _ => 1) (GeneralPaperSourceWordGrowth.tight_constant 1)) (source model))
  intro p
  exact GeneralPaperFastWholeDriverStorageRates.profile_model_mono model (GeneralPaperFastRationalMajorant.model C d)
    (GeneralPaperFastRationalMajorant.dominates hg) C d 1 (source model p).m (source model p).k (source model p).Qv (source model p).B

theorem sorted_space_at_one {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    GeneralPaperUniformResourceGrowth.Bound (fun p => GeneralPaperCachedRowConstructionStorage.profile model 1
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (source model p).m (source model p).k).lambda (source model p).k).rows
      0 (source model p).m (GeneralPaperProxyParameters.prepare (source model p).m (source model p).k).K
      (1+2*GeneralPaperSourcePairAnchorHeights.width (source model p).m (source model p).k))
      (fun p => GeneralPaperSourceRateAlgebra.monomial 2 0 3 (source model p)) (logarithm model) :=
  GeneralPaperUniformResourceGrowth.pullback_source_bound
    (GeneralPaperSortedConstructionProfileRates.native_profile hg (fun _ => 1) (GeneralPaperSourceWordGrowth.tight_constant 1)
      (fun _ => 0) GeneralPaperSourceWordGrowth.Input.m (fun _ => Nat.zero_le _) (fun _ => le_rfl)) (source model)

end Blotto.GeneralPaperNativeResourceDomain
