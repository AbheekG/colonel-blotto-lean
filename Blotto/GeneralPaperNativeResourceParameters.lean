import Blotto.GeneralPaperUniformResourceAlgebra

/-! Intrinsic parameters and the retained first-round source view on the
actual problem domain. Both rounds use existing retained data. Their source
logarithms share one uniform input-length ledger; no execution is repeated. -/
namespace Blotto.GeneralPaperNativeResourceParameters
open GeneralPaperNativeResourceDomain GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
attribute [fun_prop] GeneralPaperNativeResourceDomain.original_small GeneralPaperNativeResourceDomain.accuracy_small
  GeneralPaperNativeResourceDomain.count_small GeneralPaperNativeResourceDomain.original_input_small
  GeneralPaperNativeResourceDomain.exponent_tight

def prepared (model : RationalCostModel) (p : Problem) : GeneralPaperOriginalSourceValuePreparation.Output p.n :=
  GeneralPaperNativePreparationReferenceContract.data model (exponent p) p.values p.selector p.correct

def reduced (model : RationalCostModel) (p : Problem) : GeneralPaperReducedValuesDriver.Output p.n := (prepared model p).reduced

@[fun_prop]
theorem exponent_small (model : RationalCostModel) : Small exponent (logarithm model) :=
  small_of_tight (exponent_tight model) (logarithm_positive model)

@[fun_prop]
theorem dyadic_small (model : RationalCostModel) : Small (fun p => 2^(exponent p)) (logarithm model) :=
  power_two_small exponent _ (logarithm_positive model) (exponent_tight model)

@[fun_prop]
theorem fields_small (model : RationalCostModel) : Small (fun p => (reduced model p).m) (logarithm model) :=
  pullback_source_small GeneralPaperSourceWordGrowth.m_small (source model)

@[fun_prop]
theorem denominator_small (model : RationalCostModel) : Small (fun p => (prepared model p).Qv) (logarithm model) :=
  pullback_source_small GeneralPaperSourceWordGrowth.Qv_small (source model)

@[fun_prop]
theorem ledger_small (model : RationalCostModel) : Small ledger (logarithm model) :=
  pullback_source_small GeneralPaperSourceWordGrowth.B_small (source model)

@[fun_prop]
theorem representatives_small (model : RationalCostModel) : Small (fun p => (reduced model p).representatives) (logarithm model) := by
  have hL := logarithm_positive model
  have hk := dyadic_small model
  apply small_mono (g:=fun p => 8*2^(exponent p)) (by fun_prop)
  intro p
  change (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.representatives≤_
  rw [GeneralPaperNativeReductionShape.original_representatives,GeneralPaperLightFieldReduction.representatives]

@[fun_prop]
theorem first_denominator_small (model : RationalCostModel) : Small (fun p => (reduced model p).denominator) (logarithm model) := by
  have hL := logarithm_positive model
  have hn := count_small model
  have hk := dyadic_small model
  apply small_mono (g:=fun p => 257*p.n*2^(exponent p)) (by fun_prop)
  intro p
  exact GeneralPaperOriginalValueReduction.denominator false model 1 (exponent p) p.values p.selector p.correct

@[fun_prop]
theorem light_count_small (model : RationalCostModel) : Small (fun p => (reduced model p).classified.light.size) (logarithm model) :=
  small_mono (count_small model) (fun p => GeneralPaperStrategyPreparationWork.light_size false model 1 (exponent p) p.values)

@[fun_prop]
theorem heavy_count_small (model : RationalCostModel) : Small (fun p => (reduced model p).classified.heavy.size) (logarithm model) :=
  small_mono (count_small model) (fun p => GeneralPaperClosedArithmeticSampling.heavy_size false model 1 (exponent p) p.values)

@[fun_prop]
theorem light_mass_small (model : RationalCostModel) : Small (fun p => (reduced model p).classified.lightWeight) (logarithm model) :=
  small_mono (first_denominator_small model) (fun p => GeneralPaperNativeCircleLoss.original_mass_bound false model 1 (exponent p) p.values)

@[fun_prop]
theorem owner_small (model : RationalCostModel) (W : Problem → ℕ) (hW : Small W (logarithm model)) :
    Small (fun p => GeneralPaperOriginalReductionRetainedStorage.footprint (W p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hn := count_small model
  have hk := exponent_small model
  apply small_mono (g:=fun p => 2048*(p.n+1)*(W p+binaryWordWidth p.n+exponent p+1)) (by fun_prop)
  intro p
  exact GeneralPaperOriginalReductionRetainedStorage.original_linear false model 1 (W p) (exponent p) p.values p.selector p.correct

@[fun_prop]
theorem second_input_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperValueRoundingInputPrice.inputSize (reduced model p).values) (logarithm model) := by
  have hL := logarithm_positive model
  have hn := count_small model
  have hk := exponent_small model
  apply small_mono (g:=fun p => p.n*(512*(binaryWordWidth p.n+exponent p+1))) (by fun_prop)
  intro p
  have hm := (GeneralPaperOriginalValueReduction.count_bounds false model 1 (exponent p) p.values p.selector p.correct).2.1
  have hw := GeneralPaperOriginalReductionRetainedStorage.original_words false model 1 (exponent p) p.values p.selector p.correct
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hw j)
  have hs' : GeneralPaperValueRoundingInputPrice.inputSize (reduced model p).values≤
      (reduced model p).m*(512*(binaryWordWidth p.n+exponent p+1)) := by
    change GeneralPaperValueRoundingInputPrice.inputSize (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.values≤
      (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.m*(512*(binaryWordWidth p.n+exponent p+1))
    simpa only [GeneralPaperValueRoundingInputPrice.inputSize,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  exact hs'.trans (Nat.mul_le_mul_right _ hm)

def originalSource (model : RationalCostModel) (p : Problem) : GeneralPaperSourceWordGrowth.Input where
  m := p.n
  k := exponent p
  Qv := (reduced model p).denominator
  B := ledger p
  b := p.budget
  hb := p.budget_valid
  hB := (budget_height p).mono (by unfold ledger originalInputSize;omega)
  reciprocal := false
  weights := (reduced model p).firstWeights
  weight_sum := by
    change (∑ j,(GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.firstWeights.read j)=
      (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.denominator
    rw [(GeneralPaperOriginalValueReduction.retained false model 1 (exponent p) p.values).1,
      (GeneralPaperOriginalValueReduction.retained false model 1 (exponent p) p.values).2]
    exact GeneralPaperValueRoundingPaperContract.source_sum false model 1 256 (exponent p) p.values

theorem original_source_reduction (model : RationalCostModel) (p : Problem) :
    reduced model p=(GeneralPaperReducedValuesDriver.run false model 1 (originalSource model p).k
      (originalSource model p).Qv (originalSource model p).weights).1 := by
  change (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1=
    (GeneralPaperReducedValuesDriver.run false model 1 (exponent p)
      (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.denominator
      (GeneralPaperOriginalValueReduction.run false model 1 (exponent p) p.values).1.firstWeights).1
  rw [(GeneralPaperOriginalValueReduction.retained false model 1 (exponent p) p.values).1,
    (GeneralPaperOriginalValueReduction.retained false model 1 (exponent p) p.values).2]
  exact GeneralPaperOriginalValueReduction.data false model 1 (exponent p) p.values

@[fun_prop]
theorem original_alphabet_small (model : RationalCostModel) :
    Small (fun p => (GeneralPaperProxyParameters.alphabet p.n (exponent p)).lambda) (logarithm model) := by
  have hL := logarithm_positive model
  have hn := count_small model
  have hk := exponent_tight model
  have hks := exponent_small model
  have hSeven : Small (fun p => 2^(7+exponent p)) (logarithm model) := by fun_prop
  have hSeventeen : Small (fun p => 2^(17+exponent p)) (logarithm model) := by fun_prop
  have hDimension (p : Problem) : (GeneralPaperProxyParameters.prepare p.n (exponent p)).d≤p.n*2^(7+exponent p) := by
    rw [(GeneralPaperProxyParameters.data p.n (exponent p)).2.2.1,
      (GeneralPaperProxyParameters.data p.n (exponent p)).1,GeneralPaperScoreScaleParameters.label_power]
    exact Nat.mul_le_mul_left p.n (Nat.sub_le _ _)
  apply small_mono (g:=fun p => 24+4*(p.n*2^(7+exponent p)+2)*binaryWordWidth (p.n+3)+
    2*(p.n*(2^(17+exponent p)-1)+1)*binaryWordWidth (p.n+2)) (by fun_prop (config := {maxSteps := 4000}))
  intro p
  apply (GeneralPaperProxyWidths.lambda_bound p.n (exponent p)).trans
  rw [GeneralPaperComparatorParameters.count_power]
  gcongr
  exact hDimension p

@[fun_prop]
theorem original_source_log_tight (model : RationalCostModel) :
    Tight (fun p => GeneralPaperSourceWordGrowth.logSize (originalSource model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hn := count_small model
  have hk := exponent_tight model
  have hQ := first_denominator_small model
  have hl := original_alphabet_small model
  have hB := ledger_small model
  change Tight (fun p => 128+exponent p+binaryWordWidth (p.n+1)+
    binaryWordWidth ((GeneralPaperProxyParameters.alphabet p.n (exponent p)).lambda+1)+
    binaryWordWidth ((reduced model p).denominator+1)+binaryWordWidth (ledger p+1)) (logarithm model)
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperNativeResourceParameters
