import Blotto.GeneralPaperExactSamplerBitReturn

/-! Bounded real work of the exact retained direct/circle interface.
The direct route has no shift decoding, and every original coordinate is
written. All size/word bounds derive from the actual reduced input. -/
namespace Blotto.GeneralPaperExactSamplerArithmetic
open GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
open GeneralPaperClosedArithmeticSampling (heavy_size representative_size weight_product_word)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

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
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤65536*(n+k+1) := by
  dsimp only
  intro physical
  let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k values
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
    intro reciprocal fresh
    let c := if reciprocal then b else 1
    dsimp only [GeneralPaperExactStoredSampler.run,GeneralPaperExactStoredSampler.bits,
      GeneralPaperExactStoredSampler.shiftBits,GeneralPaperSamplingControls.specification]
    dsimp only [GeneralPaperExactStoredSampler.bits,GeneralPaperExactStoredSampler.shiftBits,
      GeneralPaperSamplingControls.specification] at fresh
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
    intro reciprocal fresh
    let c := if reciprocal then b else 1
    dsimp only [GeneralPaperExactStoredSampler.run,GeneralPaperExactStoredSampler.bits,
      GeneralPaperExactStoredSampler.shiftBits,GeneralPaperSamplingControls.specification]
    dsimp only [GeneralPaperExactStoredSampler.bits,GeneralPaperExactStoredSampler.shiftBits,
      GeneralPaperSamplingControls.specification] at fresh
    have h := GeneralPaperDirectRowExactSampler.arithmetic_work t.rowBits t.rows hRows hm c
      (if reciprocal then physical.poor else physical.rich) fresh
    dsimp only [o,t,c,hRows,rationalPrice,indexPrice] at h hDecoded ⊢
    simp only [Bool.false_eq_true,ite_false]
    nlinarith only [h,hDecoded]

end Blotto.GeneralPaperExactSamplerArithmetic
