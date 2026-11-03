import Blotto.GeneralPaperRealHeadlineParameters

/-! The actual epsilon-driven closed producer satisfies the paper's
real-RAM n+n_*^2/epsilon^5 bound, with an explicit logarithmic factor in
original n and inverse accuracy. No input-value or budget-height log enters. -/
namespace Blotto.GeneralPaperRealPreparationHeadline
open GeneralPaperRealHeadlineParameters GeneralPaperClosedStrategyDriver
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem arithmetic_time (model : RationalCostModel) :
    ∃ C d : ℕ,∀ {n : ℕ} (epsilon : ℚ) (_hE : 0<epsilon) (_hOne : epsilon<1)
      (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
      (b : ℚ),0<b ∧ b<1 →
      ((arithmetic model epsilon values v hv b).2:ℚ)≤(C:ℚ)*timeScale n epsilon*(logarithm n epsilon:ℚ)^d := by
  obtain ⟨C,d,hTime⟩ := GeneralPaperClosedSamplerWork.real_input_time model
  refine ⟨C*43808,d,?_⟩
  intro n epsilon hE hOne values v hv b hb
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  let m := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1.reduced.m
  let L := GeneralPaperOriginalSourceValueContract.inputLog n k 0
  have hNative := hTime epsilon values v hv b hb
  simp only [GeneralPaperSourceRateAlgebra.monomial,GeneralPaperNativeSourceRates.fields,
    GeneralPaperNativeSourceRates.accuracy,GeneralPaperOriginalSourceValuePreparation.input,pow_zero,Nat.mul_one] at hNative
  change (arithmetic model epsilon values v hv b).2≤C*(n+1+(m+1)^2*(2^k)^5)*L^d at hNative
  have hQ : ((arithmetic model epsilon values v hv b).2:ℚ)≤
      (C:ℚ)*((n+1+(m+1)^2*(2^k)^5:ℕ):ℚ)*(L:ℚ)^d := by exact_mod_cast hNative
  have hScale := original_scale false model 1 epsilon hE hOne values v hv
  have hLog : L≤logarithm n epsilon := log_bound n epsilon
  have hPow : (L:ℚ)^d≤(logarithm n epsilon:ℚ)^d := by exact_mod_cast Nat.pow_le_pow_left hLog d
  have hNonneg : 0≤timeScale n epsilon := by unfold timeScale;positivity
  calc
    _≤(C:ℚ)*((n+1+(m+1)^2*(2^k)^5:ℕ):ℚ)*(L:ℚ)^d := hQ
    _≤(C:ℚ)*(43808*timeScale n epsilon)*(logarithm n epsilon:ℚ)^d :=
      mul_le_mul (mul_le_mul_of_nonneg_left hScale (by positivity)) hPow (by positivity) (by positivity)
    _=((C*43808:ℕ):ℚ)*timeScale n epsilon*(logarithm n epsilon:ℚ)^d := by push_cast;ring

theorem time_and_equilibrium (model : RationalCostModel) :
    ∃ C d : ℕ,∀ {n : ℕ} (epsilon : ℚ) (_hE : 0<epsilon) (_hOne : epsilon<1)
      (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
      (b : ℚ),0<b ∧ b<1 →
      let prepared := (arithmetic model epsilon values v hv b).1
      ((arithmetic model epsilon values v hv b).2:ℚ)≤(C:ℚ)*timeScale n epsilon*(logarithm n epsilon:ℚ)^d ∧
      ∃ sampler : GeneralPaperStoredStrategySampler.Sampler n
        (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda prepared.raw.exponent).rows
        (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K,
        prepared.sampler=some sampler ∧
        GeneralPaperClosedStrategyEquilibrium.Guarantee false (fun _ => 1) 1 model v.values (b:ℝ) (epsilon:ℝ) sampler := by
  obtain ⟨C,d,h⟩ := arithmetic_time model
  refine ⟨C,d,?_⟩
  intro n epsilon hE hOne values v hv b hb
  dsimp only
  exact ⟨h epsilon hE hOne values v hv b hb,
    GeneralPaperClosedStrategyEquilibrium.arithmetic_epsilon model epsilon hE hOne values v hv b hb (fun _ => 1)⟩

end Blotto.GeneralPaperRealPreparationHeadline
