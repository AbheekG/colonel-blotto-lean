import Blotto.GeneralPaperCachedArithmeticSampling

/-! Worst-case real arithmetic work of the closed source sampler. Native
counts/weights derive the linear bound; there is no input-time, source-work
or payload-height oracle, and rational output writes are included. -/
namespace Blotto.GeneralPaperClosedArithmeticSampling
open GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

theorem heavy_size {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.heavy.size≤n := by
  have h := Fintype.card_congr (GeneralPaperLightFieldIndexEquiv.originalEquiv bits model W k values)
  simp only [Fintype.card_fin] at h
  omega

theorem representative_size {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k values).1.replaced=true) :
    (GeneralPaperOriginalValueReduction.run bits model W k values).1.representatives≤n :=
  (GeneralPaperNativeCircleLoss.original_replaced_count bits model W k values hReplace).le.trans
    (GeneralPaperStrategyPreparationWork.light_size bits model W k values)

theorem weight_product_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    binaryWordWidth (o.representatives*o.classified.lightWeight)≤binaryWordWidth n+2*k+15 := by
  have hR : binaryWordWidth (GeneralPaperOriginalValueReduction.run bits model W k values).1.representatives≤k+5 := by
    rw [GeneralPaperNativeReductionShape.original_representatives]
    unfold GeneralPaperLightFieldReduction.representatives
    have h := binaryWordWidth_mul 8 (2^k)
    rw [show binaryWordWidth 8=4 by decide,
      show binaryWordWidth (2^k)=k+1 by simp only [binaryWordWidth,Nat.log2_two_pow]] at h
    omega
  have hW := (binaryWordWidth_mono (GeneralPaperNativeCircleLoss.original_mass_bound bits model W k values)).trans
    (GeneralPaperOriginalValueReduction.denominator_word bits model W k values v hv)
  have h := binaryWordWidth_mul (GeneralPaperOriginalValueReduction.run bits model W k values).1.representatives
    (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.lightWeight
  dsimp only
  omega

theorem source_sampler_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (price index : ℕ → ℕ) (Ap : ℕ) (b : ℚ) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let description := fun (physical : GeneralPaperOriginalDrawEquilibrium.Columns t.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K) =>
      (make price index Ap o (GeneralPaperNativeReductionShape.original_shape bits model W k values)
        (GeneralPaperUnreplacedShape.original_shape bits model W k values)
        (GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k values) physical).1
    ∀ (physical : GeneralPaperOriginalDrawEquilibrium.Columns t.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K),
      let sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
        ⟨o,b,GeneralPaperSamplingControls.specification t.rows t.rowBits k hRows,description physical⟩
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        (GeneralPaperStoredStrategySampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤65536*(n+k+1) := by
  dsimp only
  intro physical reciprocal fresh
  let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k values
  let c := if reciprocal then b else 1
  have hN := (GeneralPaperOriginalValueReduction.count_bounds bits model W k values v hv).2.1
  have hBits := GeneralPaperCachedArithmeticSampling.row_bits o.m n k hN
  have hw4 : binaryWordWidth (n+4)≤n+5 := by
    have h := Nat.log2_le_self (n+4)
    unfold binaryWordWidth
    omega
  have hDecoded : t.rowBits+(k+6)≤4*k+2*n+97 := by
    dsimp only [t]
    omega
  by_cases hReplace:o.replaced=true
  · obtain ⟨hm,_⟩ := GeneralPaperNativeReductionShape.original_shape bits model W k values hReplace
    rw [make_circle price index Ap o _ _ _ physical hReplace hm]
    dsimp only [GeneralPaperStoredStrategySampler.run,GeneralPaperStrategyDescription.run,GeneralPaperSamplingControls.specification,castDescription]
    have hW := GeneralPaperCircleActualWeights.original_total_positive bits model W k values v hv
      (GeneralPaperNativeCircleLoss.original_light_positive bits model W k values hReplace)
    have h := GeneralPaperCachedArithmeticSampling.run_work model price index Ap t.rowBits (k+6) t.rows
      (GeneralPaperNativeSelectedSecurity.count k) hRows (GeneralPaperNativeSelectedSecurity.count_power k)
      o hm hR hW c physical (GeneralPaperCircleActualWeights.original_sum bits model W k values)
      (GeneralPaperLightFieldIndexEquiv.original_bijective bits model W k values) reciprocal fresh
    have hHeavy := heavy_size bits model W k values
    have hRep := representative_size bits model W k values hReplace
    have hWord := weight_product_word bits model W k values v hv
    have hw : binaryWordWidth n≤n+1 := by
      have h := Nat.log2_le_self n
      unfold binaryWordWidth
      omega
    simp only [GeneralPaperCachedCircleWork.selectedProfile,Nat.mul_one] at h
    dsimp only [o,t,c,hR,hRows] at h hHeavy hRep hWord hDecoded ⊢
    nlinarith only [h,hHeavy,hRep,hWord,hw,hDecoded]
  · have hFalse : o.replaced=false := by cases he:o.replaced <;> simp_all
    obtain ⟨hm,_⟩ := GeneralPaperUnreplacedShape.original_shape bits model W k values hFalse
    rw [make_direct price index Ap o _ _ _ physical hFalse hm]
    dsimp only [GeneralPaperStoredStrategySampler.run,GeneralPaperStrategyDescription.run,GeneralPaperSamplingControls.specification,castDescription]
    have h := GeneralPaperDirectRowSampler.run_arithmetic_work t.rowBits (k+6) t.rows (GeneralPaperNativeSelectedSecurity.count k)
      hRows (GeneralPaperNativeSelectedSecurity.count_power k) hm c (if reciprocal then physical.poor else physical.rich) fresh
    dsimp only [o,t,c,hRows,rationalPrice,indexPrice] at h hDecoded ⊢
    simp only [Bool.false_eq_true,ite_false]
    nlinarith only [h,hDecoded]


theorem arithmetic_draw_work {n : ℕ} (model : RationalCostModel) (epsilon : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    let prepared := (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1
    ∀ (sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda prepared.raw.exponent).rows
      (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K),
      prepared.sampler=some sampler →
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        (GeneralPaperStoredStrategySampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤
          131072*(n+binaryWordWidth ⌈epsilon⁻¹⌉₊) := by
  dsimp only
  intro sampler hSampler
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  obtain ⟨physical,_pair,_hSource,_hMatches,hDescription,_hWork⟩ :=
    GeneralPaperOriginalStrategyDriver.arithmetic_return model k values v hv (b:ℝ) (by exact_mod_cast hb)
  let raw := (GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).1
  let made : Description raw.strategies.original.reduced
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    (make (fun _ => 1) (fun _ => 1) 1 (GeneralPaperOriginalValueReduction.run false model 1 k values).1
      (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
      (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
      (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical).1
  let canonical : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    ⟨raw.strategies.original.reduced,b,GeneralPaperSamplingControls.specification _
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rowBits
      raw.exponent (GeneralPaperTrajectoryParameters.rows_power
        (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent),made⟩
  have hNative : (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1.sampler=some canonical :=
    GeneralPaperClosedStrategyDriver.close_some (fun _ => 1) 1 raw made hDescription
  have hEq : sampler=canonical := Option.some.inj (hSampler.symm.trans hNative)
  subst sampler
  intro reciprocal fresh
  have hWork := source_sampler_work false model 1 k values v hv (fun _ => 1) (fun _ => 1) 1 b physical reciprocal fresh
  have hk : k≤binaryWordWidth ⌈epsilon⁻¹⌉₊ := GeneralPaperRealHeadlineParameters.exponent_bound epsilon
  have hn : 1≤n := v.fields_positive
  exact hWork.trans (by nlinarith only [hk,hn])

theorem headline_with_draws (model : RationalCostModel) :
    ∃ C d : ℕ,∀ {n : ℕ} (epsilon : ℚ) (_hE : 0<epsilon) (_hOne : epsilon<1)
      (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
      (b : ℚ),0<b ∧ b<1 →
      let prepared := (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1
      ((GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).2:ℚ)≤
        (C:ℚ)*GeneralPaperRealHeadlineParameters.timeScale n epsilon*(GeneralPaperRealHeadlineParameters.logarithm n epsilon:ℚ)^d ∧
      ∃ sampler : Sampler n
        (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda prepared.raw.exponent).rows
        (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K,
        prepared.sampler=some sampler ∧
        GeneralPaperClosedStrategyEquilibrium.Guarantee false (fun _ => 1) 1 model v.values (b:ℝ) (epsilon:ℝ) sampler ∧
        ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
          (GeneralPaperStoredStrategySampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤
            131072*(n+binaryWordWidth ⌈epsilon⁻¹⌉₊) ∧
          (GeneralPaperStoredStrategySampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).freshReads=
            Nat.log2 (sampler.controls.rows*sampler.controls.shifts) := by
  obtain ⟨C,d,h⟩ := GeneralPaperRealPreparationHeadline.time_and_equilibrium model
  refine ⟨C,d,?_⟩
  intro n epsilon hE hOne values v hv b hb
  obtain ⟨hTime,sampler,hSampler,hGuarantee⟩ := h epsilon hE hOne values v hv b hb
  refine ⟨hTime,sampler,hSampler,hGuarantee,?_⟩
  intro reciprocal fresh
  exact ⟨arithmetic_draw_work model epsilon values v hv b hb sampler hSampler reciprocal fresh,
    logarithmic_bits false (fun _ => 1) 1 model sampler reciprocal fresh⟩

end Blotto.GeneralPaperClosedArithmeticSampling
