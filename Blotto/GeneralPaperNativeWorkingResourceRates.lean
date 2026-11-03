import Blotto.GeneralPaperUniformResourceRates

/-! Sharp working-space bounds on actual original inputs. Original input
precision and accuracy encoding enter additively through the native ledger.
Unconditional first-round/source envelopes retain their uniform constants. -/
namespace Blotto.GeneralPaperNativeWorkingResourceRates
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def rate (model : RationalCostModel) (p : Problem) : ℕ :=
  ledger p+1+GeneralPaperSourceRateAlgebra.monomial 3 0 4 (source model p)

theorem rate_positive (model : RationalCostModel) : ∀ p,1≤rate model p := by intro p;unfold rate;omega

theorem count_ledger (p : Problem) : p.n≤ledger p := by
  have h := GeneralPaperOriginalValueBitDriverRate.input_fields p.values
  change p.n≤originalSize p at h
  unfold ledger originalInputSize
  omega

@[fun_prop]
theorem count_bound (model : RationalCostModel) : Bound Problem.n (rate model) (logarithm model) :=
  pointwise _ _ _ 1 (fun p => by have h := count_ledger p;unfold rate;omega)

@[fun_prop]
theorem ledger_bound (model : RationalCostModel) : Bound ledger (rate model) (logarithm model) :=
  pointwise _ _ _ 1 (fun p => by unfold rate;omega)

@[fun_prop]
theorem original_bound (model : RationalCostModel) : Bound originalSize (rate model) (logarithm model) :=
  pointwise _ _ _ 1 (fun p => by unfold rate ledger originalInputSize;omega)

@[fun_prop]
theorem accuracy_bound (model : RationalCostModel) : Bound accuracySize (rate model) (logarithm model) :=
  pointwise _ _ _ 1 (fun p => by unfold rate ledger;omega)

@[fun_prop]
theorem fields_bound (model : RationalCostModel) : Bound (fun p => (reduced model p).m) (rate model) (logarithm model) :=
  dominated (count_bound model) (fun p => (GeneralPaperOriginalSourceValuePreparation.count_bounds false model 1 (exponent p) p.values p.selector p.correct).2.1)

@[fun_prop]
theorem light_bound (model : RationalCostModel) : Bound (fun p => (reduced model p).classified.light.size) (rate model) (logarithm model) :=
  dominated (count_bound model) (fun p => GeneralPaperStrategyPreparationWork.light_size false model 1 (exponent p) p.values)

@[fun_prop]
theorem heavy_bound (model : RationalCostModel) : Bound (fun p => (reduced model p).classified.heavy.size) (rate model) (logarithm model) :=
  dominated (count_bound model) (fun p => GeneralPaperClosedArithmeticSampling.heavy_size false model 1 (exponent p) p.values)

theorem preparation_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalSourcePreparationStorage.preparationProfile model 1 (exponent p) (originalSize p)
      (reduced model p).denominator (GeneralPaperValueRoundingInputPrice.inputSize (reduced model p).values) (reduced model p))
      (rate model) (logarithm model) := by
  have hEnvelope := pullback_bound_with_log (GeneralPaperReducedInputPreparationGrowth.preparation_rate hg)
    (originalSource model) (logarithm model) (original_source_log_tight model)
  have hRate := rate_comparison hEnvelope 10 (fun p => by
    have hn := count_ledger p
    have hR : (reduced model p).representatives≤8*2^(exponent p) := by
      change (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.representatives≤_
      rw [GeneralPaperNativeReductionShape.original_representatives,GeneralPaperLightFieldReduction.representatives]
    have ha : 2^(exponent p)≤GeneralPaperSourceRateAlgebra.monomial 3 0 4 (source model p) := by
      have hm := GeneralPaperSourceRateAlgebra.monomial_mono (a:=0) (b:=0) (c:=1) (a':=3) (b':=0) (c':=4) (by omega) (by omega) (by omega) (source model p)
      simpa only [GeneralPaperSourceRateAlgebra.monomial,pow_zero,pow_one,Nat.one_mul,
        GeneralPaperNativeSourceRates.accuracy,source_exponent] using hm
    change ledger p+p.n+(GeneralPaperReducedInputPreparationGrowth.output model (originalSource model p)).representatives+1≤10*rate model p
    unfold GeneralPaperReducedInputPreparationGrowth.output
    rw [←original_source_reduction model p]
    unfold rate
    omega)
  apply dominated hRate
  intro p
  change _≤GeneralPaperOriginalSourcePreparationStorage.preparationProfile model 1 (exponent p) (ledger p)
    (reduced model p).denominator
    (GeneralPaperValueRoundingInputPrice.inputSize (GeneralPaperReducedInputPreparationGrowth.output model (originalSource model p)).values)
    (GeneralPaperReducedInputPreparationGrowth.output model (originalSource model p))
  unfold GeneralPaperReducedInputPreparationGrowth.output
  rw [←original_source_reduction model p]
  exact GeneralPaperReducedInputPreparationGrowth.preparation_profile_mono model 1 (exponent p) (originalSize p) (ledger p)
    (reduced model p).denominator _ (reduced model p) (by unfold ledger originalInputSize;omega)

theorem whole_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperFastWholeDriverStorage.profile model C d 1 (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)) (rate model) (logarithm model) := whole_space_at_one hg

theorem owner_rate (model : RationalCostModel) :
    Bound (fun p => GeneralPaperOriginalReductionRetainedStorage.footprint 1 (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hCoefficient : Polylog (fun p => 1+binaryWordWidth p.n+exponent p+1) (logarithm model) := by
    have hk := polylog_of_tight (exponent_tight model)
    fun_prop
  apply dominated (g:=fun p => 2048*(p.n+1)*(1+binaryWordWidth p.n+exponent p+1)) (by fun_prop)
  intro p
  exact GeneralPaperOriginalReductionRetainedStorage.original_linear false model 1 1 (exponent p) p.values p.selector p.correct

theorem row_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (rowEnvelope model) (rate model) (logarithm model) := by
  have h := pullback_source_bound (GeneralPaperSortedConstructionProfileRates.native_profile hg (fun _ => 1)
    (GeneralPaperSourceWordGrowth.tight_constant 1) GeneralPaperSourceWordGrowth.Input.m GeneralPaperSourceWordGrowth.Input.m
    (fun _ => le_rfl) (fun _ => le_rfl)) (source model)
  apply rate_mono h
  intro p
  have hm := GeneralPaperSourceRateAlgebra.monomial_mono (a:=2) (b:=0) (c:=3) (a':=3) (b':=0) (c':=4) (by omega) (by omega) (by omega) (source model p)
  unfold rate
  omega

end Blotto.GeneralPaperNativeWorkingResourceRates
