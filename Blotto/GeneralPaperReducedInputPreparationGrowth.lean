import Blotto.GeneralPaperNativeResourceParameters

/-! Unconditional first-round source-record envelopes. This domain carries
the already retained first weights and denominator, so its native reduction
exists even for degenerate source records. No arbitrary-source/native-input
matching premise is assumed. The original problem pulls these bounds back. -/
namespace Blotto.GeneralPaperReducedInputPreparationGrowth
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCacheConstructionGrowth GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def output (model : RationalCostModel) (x : Input) : GeneralPaperReducedValuesDriver.Output x.m :=
  (GeneralPaperReducedValuesDriver.run false model 1 x.k x.Qv x.weights).1

def valueWidth (x : Input) : ℕ := GeneralPaperReducedValueArrayPrice.width x.Qv (GeneralPaperLightFieldReduction.representatives x.k)

theorem parameters (model : RationalCostModel) (x : Input) :
    (output model x).firstWeights=x.weights ∧ (output model x).denominator=x.Qv ∧
    (output model x).representatives=GeneralPaperLightFieldReduction.representatives x.k ∧
    (output model x).m≤x.m ∧ (output model x).classified.heavy.size≤x.m ∧
    (output model x).classified.light.size≤x.m ∧ (output model x).classified.lightWeight≤x.Qv ∧
    GeneralPaperOriginalReductionRetainedStorage.ValuesWords (output model x) (valueWidth x) := by
  have hr := GeneralPaperReducedValuesDriver.retained false model 1 x.k x.Qv x.weights
  have hm := (GeneralPaperReducedValuesConstructionStorage.native_data model 1 x.k x.Qv x.weights).2.2.2
  rw [GeneralPaperReducedValuesDriver.models_data model 1 x.k x.Qv x.weights] at hm
  have hSizes : (output model x).classified.heavy.size+(output model x).classified.light.size=x.m := by
    unfold output
    rw [hr.2.2.1]
    exact GeneralPaperReducedValuesPrice.sizes false model 1 x.k x.Qv x.weights
  have hMass := GeneralPaperNativeCircleLoss.reduced_mass_bound false model 1 x.k x.Qv x.weights x.weight_sum
  change (output model x).classified.lightWeight≤(output model x).denominator at hMass
  have hd : (output model x).denominator=x.Qv := hr.2.1
  rw [hd] at hMass
  refine ⟨?_,hd,?_,hm,by omega,by omega,hMass,?_⟩
  · exact (GeneralPaperReducedValuesDriver.retained false model 1 x.k x.Qv x.weights).1
  · exact (GeneralPaperReducedValuesDriver.retained false model 1 x.k x.Qv x.weights).2.2.2
  · exact GeneralPaperOriginalReductionRetainedStorage.reduced_words false model 1 x.k x.Qv x.weights x.weight_sum

theorem representatives_small (model : RationalCostModel) : Small (fun x => (output model x).representatives) := by
  have hp := pow_two _ k_tight
  apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 8*2^x.k) (by fun_prop)
  intro x
  rw [(parameters model x).2.2.1,GeneralPaperLightFieldReduction.representatives]

theorem value_width_poly : Polylog valueWidth := by
  have hp := pow_two _ k_tight
  unfold valueWidth GeneralPaperReducedValueArrayPrice.width GeneralPaperLightFieldReduction.representatives
  fun_prop

theorem short_input_rate (model : RationalCostModel) : Linear (fun x => GeneralPaperValueRoundingInputPrice.inputSize (output model x).values) Input.m := by
  apply GeneralPaperSourceSoftBounds.dominated (mul_poly (linear_identity Input.m) value_width_poly)
  intro x
  have h := parameters model x
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => h.2.2.2.2.2.2.2 j)
  have hs' : GeneralPaperValueRoundingInputPrice.inputSize (output model x).values≤(output model x).m*valueWidth x := by
    simpa only [GeneralPaperValueRoundingInputPrice.inputSize,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  exact hs'.trans (Nat.mul_le_mul_right _ h.2.2.2.1)

theorem profile_mono_fields (W n m m' Q R V : ℕ) (h : m≤m') :
    GeneralPaperOriginalReductionRetainedStorage.profile W n m Q R V≤
      GeneralPaperOriginalReductionRetainedStorage.profile W n m' Q R V := by
  unfold GeneralPaperOriginalReductionRetainedStorage.profile arrayProfile natBits
  gcongr

theorem owner_linear (model : RationalCostModel) : Linear
    (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint
      (GeneralPaperOriginalSourcePreparationStorage.reference 1 (output model x)) (output model x)) Input.m := by
  have hR := representatives_small model
  have hWidth := value_width_poly
  have hReference : Polylog (fun x => GeneralPaperOriginalSourcePreparationStorage.reference 1 (output model x)) := by
    unfold GeneralPaperOriginalSourcePreparationStorage.reference GeneralPaperReducedValuesConstructionStorage.reference arrayWord
    fun_prop
  have hUpper : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.profile
      (GeneralPaperOriginalSourcePreparationStorage.reference 1 (output model x)) x.m x.m x.Qv
      (output model x).representatives (valueWidth x)) Input.m := by
    unfold GeneralPaperOriginalReductionRetainedStorage.profile arrayProfile natBits
    fun_prop (config := {maxSteps := 4000})
  apply GeneralPaperSourceSoftBounds.dominated hUpper
  intro x
  have h := parameters model x
  have hWeights (j : Fin x.m) : (output model x).firstWeights.read j≤(output model x).denominator := by
    rw [h.1,h.2.1,←x.weight_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hBound := GeneralPaperOriginalReductionRetainedStorage.bounded
    (GeneralPaperOriginalSourcePreparationStorage.reference 1 (output model x)) (valueWidth x) (output model x)
    hWeights h.2.2.2.2.1 h.2.2.2.2.2.1 (by rw [h.2.1];exact h.2.2.2.2.2.2.1) h.2.2.2.2.2.2.2
  rw [h.2.1] at hBound
  exact hBound.trans (profile_mono_fields _ _ _ _ _ _ _ h.2.2.2.1)

theorem preparation_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Soft (fun x => x.B+x.m+(output model x).representatives+1)
      (fun x => GeneralPaperOriginalSourcePreparationStorage.preparationProfile model 1 x.k x.B x.Qv
        (GeneralPaperValueRoundingInputPrice.inputSize (output model x).values) (output model x)) := by
  have hR := representatives_small model
  have hSecondRate := short_input_rate model
  have hSecond : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (output model x).values) :=
    GeneralPaperSourceRowsStorageRates.soft_small hSecondRate (by fun_prop)
  exact GeneralPaperOriginalSourcePreparationStorage.preparation_profile_rate hg (fun _ => 1) Input.m Input.B Input.Qv
    (fun x => GeneralPaperValueRoundingInputPrice.inputSize (output model x).values) (output model)
    (tight_constant 1) m_small B_small Qv_small hSecond hSecondRate
    (fun x => (parameters model x).2.2.2.1) hR (fun x => (parameters model x).2.2.2.2.1) (owner_linear model)

theorem preparation_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun x => GeneralPaperOriginalSourcePreparationStorage.preparationProfile model 1 x.k x.B x.Qv
      (GeneralPaperValueRoundingInputPrice.inputSize (output model x).values) (output model x)) := by
  have hR := representatives_small model
  exact GeneralPaperSourceRowsStorageRates.soft_small (preparation_rate hg) (by fun_prop)

theorem preparation_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun x => GeneralPaperOriginalSourcePreparationStorage.preparationPrice model 1 x.k x.B x.Qv
      (GeneralPaperValueRoundingInputPrice.inputSize (output model x).values) (output model x)) := by
  have hR := representatives_small model
  have hSecond : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (output model x).values) :=
    GeneralPaperSourceRowsStorageRates.soft_small (short_input_rate model) (by fun_prop)
  have hM := GeneralPaperSourceWordGrowth.dominated m_small (fun x => (parameters model x).2.2.2.1)
  have hReduction := GeneralPaperOriginalSourcePreparationStorage.reduction_price_small hg (fun _ => 1) Input.m Input.B Input.Qv
    (output model) (tight_constant 1) m_small B_small Qv_small hR (fun x => (parameters model x).2.2.2.2.1)
  have hSecondPrice := GeneralPaperOriginalSourcePreparationStorage.rounding_price_small hg (fun _ => 1) (fun _ => 512)
    (fun x => (output model x).m) (fun x => GeneralPaperValueRoundingInputPrice.inputSize (output model x).values)
    (tight_constant 1) (small_constant 512) hM hSecond
  unfold GeneralPaperOriginalSourcePreparationStorage.preparationPrice GeneralPaperOriginalSourcePreparationStorage.reference
    GeneralPaperReducedValuesConstructionStorage.reference arrayWord
  fun_prop (config := {maxSteps := 4000})

theorem driver_price_mono (model : RationalCostModel) (W n M S T : ℕ) (h : S≤T) :
    GeneralPaperValueWeightSumConstructionStorage.driverPrice model W n M S≤
      GeneralPaperValueWeightSumConstructionStorage.driverPrice model W n M T := by
  unfold GeneralPaperValueWeightSumConstructionStorage.driverPrice GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice
    GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth
  dsimp only
  gcongr
  exact model.monotone (by omega)

theorem round_profile_mono (model : RationalCostModel) (W n M S T : ℕ) (h : S≤T) :
    GeneralPaperOriginalValueRoundConstructionStorage.profile model W n M S≤
      GeneralPaperOriginalValueRoundConstructionStorage.profile model W n M T := by
  unfold GeneralPaperOriginalValueRoundConstructionStorage.profile GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth
    GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice
    GeneralPaperOriginalValueRoundConstructionStorage.callbackProfile GeneralPaperOriginalValueRoundConstructionStorage.scalarProfile
    GeneralPaperOriginalValueRoundConstructionStorage.cap GeneralPaperPositiveCeilingConstructionStorage.profile
    GeneralPaperPositiveCeilingConstructionStorage.price GeneralPaperNativePayloadFillStorage.profile
    GeneralPaperNativePayloadFillStorage.frameProfile GeneralPaperNativePayloadFillStorage.metadataCap
    GeneralPaperNativePayloadFillStorage.workCap natBits
  dsimp only [GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice,GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice]
  gcongr <;> exact model.monotone (by omega)

theorem driver_profile_mono (model : RationalCostModel) (W n M S T : ℕ) (h : S≤T) :
    GeneralPaperValueWeightSumConstructionStorage.driverProfile model W n M S≤
      GeneralPaperValueWeightSumConstructionStorage.driverProfile model W n M T := by
  have hPrice := driver_price_mono model W n M S T h
  have hRound := round_profile_mono model W n M S T h
  unfold GeneralPaperValueWeightSumConstructionStorage.driverProfile natBits
  dsimp only
  gcongr

theorem rounding_price_mono (model : RationalCostModel) (W c n k S T : ℕ) (h : S≤T) :
    GeneralPaperNativeScaleConstructionStorage.roundingPrice model W c n k S≤
      GeneralPaperNativeScaleConstructionStorage.roundingPrice model W c n k T := by
  unfold GeneralPaperNativeScaleConstructionStorage.roundingPrice
  exact Nat.add_le_add_right (Nat.add_le_add_left (driver_price_mono model W n _ S T h) _) _

theorem rounding_profile_mono (model : RationalCostModel) (W c n k S T : ℕ) (h : S≤T) :
    GeneralPaperNativeScaleConstructionStorage.roundingProfile model W c n k S≤
      GeneralPaperNativeScaleConstructionStorage.roundingProfile model W c n k T := by
  have hPrice := rounding_price_mono model W c n k S T h
  have hRound := driver_profile_mono model W n (GeneralPaperValueRoundingPaperContract.scale c n k) S T h
  unfold GeneralPaperNativeScaleConstructionStorage.roundingProfile GeneralPaperNativeScaleConstructionStorage.roundingCap natBits
  gcongr

theorem preparation_price_mono {n : ℕ} (model : RationalCostModel) (W k S T Q S₂ : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (h : S≤T) :
    GeneralPaperOriginalSourcePreparationStorage.preparationPrice model W k S Q S₂ o≤
      GeneralPaperOriginalSourcePreparationStorage.preparationPrice model W k T Q S₂ o := by
  have hp := rounding_price_mono model W 256 n k S T h
  unfold GeneralPaperOriginalSourcePreparationStorage.preparationPrice GeneralPaperOriginalSourcePreparationStorage.reductionPrice
  omega

theorem preparation_profile_mono {n : ℕ} (model : RationalCostModel) (W k S T Q S₂ : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (h : S≤T) :
    GeneralPaperOriginalSourcePreparationStorage.preparationProfile model W k S Q S₂ o≤
      GeneralPaperOriginalSourcePreparationStorage.preparationProfile model W k T Q S₂ o := by
  have hPrice := preparation_price_mono model W k S T Q S₂ o h
  have hFirstPrice := rounding_price_mono model W 256 n k S T h
  have hFirst := rounding_profile_mono model W 256 n k S T h
  unfold GeneralPaperOriginalSourcePreparationStorage.preparationProfile GeneralPaperOriginalSourcePreparationStorage.reductionProfile
    GeneralPaperOriginalSourcePreparationStorage.preparationCap GeneralPaperOriginalSourcePreparationStorage.reductionCap
    GeneralPaperOriginalSourcePreparationStorage.reductionPrice natBits
  gcongr

end Blotto.GeneralPaperReducedInputPreparationGrowth
