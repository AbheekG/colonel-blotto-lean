import Blotto.GeneralPaperSharpSourceRealContract

/-! Actual native input and parameter rates used by simultaneous storage.
Budget words are derived from the classified proxy, and the rounded-value
array is bounded by its actual sum. No storage or height oracle is supplied. -/
namespace Blotto.GeneralPaperSourceStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperNativeSourceWordGrowth GeneralPaperSourceSoftBounds
open GeneralPaperNativeSourceRates GeneralPaperSourceRateAlgebra GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem epochs : Rated (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) 0 1 1 :=
  GeneralPaperSharpSourceBitRate.epoch_rate

@[fun_prop]
theorem rows : Rated (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows) 0 1 2 :=
  GeneralPaperSharpSourceBitRate.rows_rate

@[fun_prop]
theorem own_word : Rated (fun x => rationalWordWidth (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)) 0 1 0 := by
  apply bounded 3
  intro x
  have h := GeneralPaperSourceBudgetWidths.own_word x.m x.k (x.b:ℝ) (by exact_mod_cast x.hb) x.reciprocal
  dsimp only [GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height] at h
  change rationalWordWidth (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)≤1+2*((alphabet x).lambda+1) at h
  simp only [monomial,pow_zero,pow_one,Nat.one_mul,Nat.mul_one,symbols]
  omega

@[fun_prop]
theorem opposing_word : Rated (fun x => rationalWordWidth (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)) 0 1 0 := by
  apply bounded 3
  intro x
  have h := GeneralPaperSourceBudgetWidths.opposing_word x.m x.k (x.b:ℝ) (by exact_mod_cast x.hb) x.reciprocal
  dsimp only [GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height] at h
  change rationalWordWidth (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)≤1+2*((alphabet x).lambda+1) at h
  simp only [monomial,pow_zero,pow_one,Nat.one_mul,Nat.mul_one,symbols]
  omega

def weightsBound (W : Input → ℕ) (x : Input) : ℕ := x.m*(1+binaryWordWidth x.Qv+W x)+32*W x

def weightsCertificate (W : Input → ℕ) (hW : Tight W) : Certificate (weightsBound W) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by unfold weightsBound; fun_prop⟩

theorem weights_degrees (W : Input → ℕ) (hW : Tight W) :
    ((weightsCertificate W hW).fields,(weightsCertificate W hW).symbols,(weightsCertificate W hW).accuracy)=(1,0,0) := rfl

theorem weights_bound (W : Input → ℕ) (x : Input) :
    GeneralPaperEncodedNatArray.footprint (W x) x.weights≤weightsBound W x :=
  GeneralPaperEncodedNatArray.bounded (W x) _ x.weights (fun j => Nat.add_le_add_left
    (binaryWordWidth_mono (GeneralPaperSourceScoreHeights.weight_le x.Qv x.weights x.weight_sum j)) 1)

@[fun_prop]
theorem weight_array (W : Input → ℕ) (hW : Tight W) :
    Rated (fun x => GeneralPaperEncodedNatArray.footprint (W x) x.weights) 1 0 0 :=
  dominated (weightsCertificate W hW).bound (weights_bound W)

@[fun_prop]
theorem weight_array_small (W : Input → ℕ) (hW : Tight W) :
    Small (fun x => GeneralPaperEncodedNatArray.footprint (W x) x.weights) := by
  have hw := of_tight hW
  apply GeneralPaperSourceWordGrowth.dominated (g:=weightsBound W)
  · fun_prop [weightsBound]
  · exact weights_bound W

@[fun_prop]
theorem resource_height : Rated (fun x => expressionHeightBudget ((alphabet x).lambda+1)
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) 1 1 0 := by
  have hr : Rated (fun x => GeneralPaperFastRootPrice.rootWord x.m (symbols x)) 1 1 0 := by
    simpa only [Rated,Soft,monomial,GeneralPaperSharpDPSourceRate.resourceRate,pow_zero,pow_one,Nat.mul_one] using
      GeneralPaperSharpDPSourceRate.root_resource_rate
  apply dominated hr
  intro x
  have h := GeneralPaperFastRootPrice.root_word_bound x.m (alphabet x).lambda x.k x.Qv ((alphabet x).lambda+1)
  dsimp only [GeneralPaperTagHeight.word] at h
  exact (show expressionHeightBudget ((alphabet x).lambda+1)
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height≤
      1+2*expressionHeightBudget ((alphabet x).lambda+1)
        (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height by omega).trans h

@[fun_prop]
theorem profit_exponent : Rated (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent) 0 0 0 :=
  poly (poly_tight _ profit_exponent_tight)

@[fun_prop]
theorem profit_q_word : Rated (fun x => binaryWordWidth (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).qProf) 0 0 0 :=
  GeneralPaperSourceRateAlgebra.word _ profit_q_small

@[fun_prop]
theorem precision_bits : Rated (fun x => (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).fractionalBits) 0 0 0 :=
  poly (poly_tight _ precision_bits_tight)

@[fun_prop]
theorem precision_columns : Rated (fun x => (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).columns) 0 0 0 :=
  poly (poly_tight _ precision_columns_tight)

@[fun_prop]
theorem denominator_word : Rated (fun x => binaryWordWidth (alphabet x).D) 0 1 0 := by
  apply dominated GeneralPaperSourceRateAlgebra.scale_word
  intro x
  exact binaryWordWidth_mono (GeneralPaperSourceAlphabetLower.order_le_scale (alphabet x))

@[fun_prop]
theorem profit_width : Rated (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width) 0 0 1 := by
  have hM : Rated (fun x => 8*GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv) 0 0 0 :=
    GeneralPaperSourceRateAlgebra.mul _ _ 0 0 0 0 0 0 (constant 8) GeneralPaperSourceRateAlgebra.measure
  have hu := GeneralPaperSourceRateAlgebra.mul _ _ 0 0 0 0 0 1 hM (dyadic_accuracy 25)
  exact dominated hu (fun x => GeneralPaperFastDPParameterSizes.width_bound x.m (alphabet x).lambda x.k x.Qv)

@[fun_prop]
theorem profit_width_word : Rated (fun x => binaryWordWidth (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width) 0 0 0 :=
  GeneralPaperSourceRateAlgebra.word _ profit_width_small

@[fun_prop]
theorem precall_measure : Rated (fun x => GeneralPaperPrecallControlWord.measure x.m x.k) 0 1 0 := by
  have hl : Rated (fun x => 8*(alphabet x).lambda) 0 1 0 :=
    GeneralPaperSourceRateAlgebra.mul _ _ 0 0 0 0 1 0 (constant 8) GeneralPaperSourceRateAlgebra.lambda
  have hs : Rated (fun x => x.k+8*(alphabet x).lambda) 0 1 0 :=
    GeneralPaperSourceRateAlgebra.add _ _ 0 0 0 0 1 0 GeneralPaperSourceRateAlgebra.k hl
  have hu := GeneralPaperSourceRateAlgebra.add _ _ 0 1 0 0 0 0 hs (constant 64)
  exact dominated hu (fun x => GeneralPaperPrecallWordEnvelope.measure_bound x.m x.k)

@[fun_prop]
theorem precall_measure_small : Small (fun x => GeneralPaperPrecallControlWord.measure x.m x.k) := by
  apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => x.k+8*(alphabet x).lambda+64)
  · fun_prop
  · exact fun x => GeneralPaperPrecallWordEnvelope.measure_bound x.m x.k

@[fun_prop]
theorem precall_measure_word : Rated (fun x => binaryWordWidth (GeneralPaperPrecallControlWord.measure x.m x.k)) 0 0 0 :=
  GeneralPaperSourceRateAlgebra.word _ precall_measure_small

@[fun_prop]
theorem proxy_cap_word : Rated (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar) 0 1 0 :=
  dominated denominator_word (fun x => binaryWordWidth_mono (GeneralPaperSourceAlphabetLower.cap_le_order x.m x.k))

@[fun_prop]
theorem proxy_grid_word : Rated (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).Qg) 0 1 0 := by
  apply dominated denominator_word
  intro x
  have h := GeneralPaperSourceAlphabetLower.cap_le_order x.m x.k
  have hq := (GeneralPaperProxyParameters.data x.m x.k).2.2.2.2.2.2
  exact binaryWordWidth_mono (show (GeneralPaperProxyParameters.prepare x.m x.k).Qg≤(alphabet x).D by
    change (GeneralPaperProxyParameters.prepare x.m x.k).qbar≤(alphabet x).D at h
    omega)

@[fun_prop]
theorem proxy_root_word : Rated (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H) 0 1 0 :=
  dominated denominator_word (fun x => binaryWordWidth_mono (GeneralPaperPrecallWordEnvelope.root_order x.m x.k))

@[fun_prop]
theorem proxy_grid_bits : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).gridBits) 0 1 0 := by
  apply dominated precall_measure
  intro x
  have h := (GeneralPaperPrecallControlWord.root_controls x.m x.k).1
  change (GeneralPaperProxyParameters.prepare x.m x.k).gridBits+4≤GeneralPaperPrecallControlWord.measure x.m x.k at h
  omega

@[fun_prop]
theorem proxy_grid_bits_small : Small (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).gridBits) := by
  apply GeneralPaperSourceWordGrowth.dominated precall_measure_small
  intro x
  have h := (GeneralPaperPrecallControlWord.root_controls x.m x.k).1
  change (GeneralPaperProxyParameters.prepare x.m x.k).gridBits+4≤GeneralPaperPrecallControlWord.measure x.m x.k at h
  omega

@[fun_prop]
theorem proxy_grid_word_small : Small (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).Qg) := by
  apply GeneralPaperSourceWordGrowth.dominated denominator_word_small
  intro x
  have h := GeneralPaperSourceAlphabetLower.cap_le_order x.m x.k
  have hq := (GeneralPaperProxyParameters.data x.m x.k).2.2.2.2.2.2
  exact binaryWordWidth_mono (show (GeneralPaperProxyParameters.prepare x.m x.k).Qg≤(alphabet x).D by
    change (GeneralPaperProxyParameters.prepare x.m x.k).qbar≤(alphabet x).D at h
    omega)

@[fun_prop]
theorem proxy_root_word_small : Small (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H) :=
  GeneralPaperSourceWordGrowth.dominated denominator_word_small (fun x =>
    binaryWordWidth_mono (GeneralPaperPrecallWordEnvelope.root_order x.m x.k))

@[fun_prop]
theorem mesh_word : Rated (fun x => binaryWordWidth (GeneralPaperSourceParameters.prepare x.k).meshDenominator) 0 0 0 :=
  GeneralPaperSourceRateAlgebra.word _ mesh_small

@[fun_prop]
theorem ceiling_depth (f : Input → ℕ) (a b c : ℕ) (hf : Rated (fun x => binaryWordWidth (f x)) a b c) :
    Rated (fun x => (GeneralPaperPowerCeiling.ceiling (f x)).doublings) a b c :=
  dominated hf (fun _x => GeneralPaperConstructedWordGrowth.ceiling_depth_bound _)

@[fun_prop]
theorem dyadic_word (f : Input → ℕ) (a b c : ℕ) (hf : Rated f a b c) :
    Rated (fun x => binaryWordWidth (2^(f x))) a b c := by
  have hmul : Rated (fun x => 2*f x) a b c := by
    simpa only [Nat.zero_add] using GeneralPaperSourceRateAlgebra.mul _ _ 0 0 0 a b c (constant 2) hf
  have hu := GeneralPaperSourceRateAlgebra.add _ _ a b c 0 0 0 hmul (constant 1)
  have hu' : Rated (fun x => 2*f x+1) a b c := by simpa only [Nat.max_zero] using hu
  apply dominated hu'
  intro x
  have h := GeneralPaperFastRationalBounds.word_power 2 (f x)
  rw [show binaryWordWidth 2=2 by decide] at h
  omega

@[fun_prop]
theorem ceiling_power_word (f : Input → ℕ) (a b c : ℕ) (hf : Rated (fun x => binaryWordWidth (f x)) a b c) :
    Rated (fun x => binaryWordWidth (GeneralPaperPowerCeiling.ceiling (f x)).power) a b c := by
  have hu := GeneralPaperSourceRateAlgebra.add _ _ 0 0 0 a b c (constant 4) hf
  have hu' : Rated (fun x => 4+binaryWordWidth (f x)) a b c := by simpa only [Nat.zero_max] using hu
  exact dominated hu' (fun _x => GeneralPaperParameterOperandBounds.ceiling_word _)

def forestCertificate  (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperEncodedForestStorage.profile (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
      GeneralPaperEncodedForestStorage.profile
      GeneralPaperSparseNodeBits.perNode
      GeneralPaperRetainedForestNodes.perField
      GeneralPaperBatchCounterPrice.limit
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 16000})⟩

theorem forest_degrees  (W : Input → ℕ) (hW : Tight W) :
    ((forestCertificate W hW).fields,(forestCertificate W hW).symbols,(forestCertificate W hW).accuracy)=(1, 2, 2) := rfl

def trajectoryCertificate  (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => GeneralPaperEncodedTrajectoryStorage.profile (W x) x.m (alphabet x).lambda x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hwa := weight_array W hW
  have hwas := weight_array_small W hW
  refine ⟨_,_,_,by
    unfold
      GeneralPaperEncodedTrajectoryStorage.profile
      GeneralPaperDecoderControls.operandWidth
    try dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 16000})⟩

theorem trajectory_degrees  (W : Input → ℕ) (hW : Tight W) :
    ((trajectoryCertificate W hW).fields,(trajectoryCertificate W hW).symbols,(trajectoryCertificate W hW).accuracy)=(1, 2, 2) := rfl

@[fun_prop]
theorem forest_rate (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperEncodedForestStorage.profile (W x) x.m (alphabet x).lambda x.k x.Qv) 1 2 2 :=
  (forestCertificate W hW).bound

@[fun_prop]
theorem trajectory_rate (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperEncodedTrajectoryStorage.profile (W x) x.m (alphabet x).lambda x.k) 1 2 2 :=
  (trajectoryCertificate W hW).bound

end Blotto.GeneralPaperSourceStorageRates
