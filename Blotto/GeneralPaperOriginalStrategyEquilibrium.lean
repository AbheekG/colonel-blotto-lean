import Blotto.GeneralPaperOriginalStrategyDriver

/-! Both actual reduction branches join one original-input prepared
strategy interface. No branch flag, source success, physical matching or
law guarantee is supplied. Every fresh-bit output respects its budget. -/
namespace Blotto.GeneralPaperOriginalStrategyEquilibrium
open GeneralPaperStrategyDescription GeneralPaperOriginalStrategyDriver
open GeneralPaperOriginalDrawEquilibrium GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem bit_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws A k : ℕ)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      (bit model Wv Ws A k values v hv b hb).1.description=some description ∧
      let μ := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description b true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  cases hFlag:(GeneralPaperOriginalValueReduction.run true model Wv k values).1.replaced with
  | false =>
    obtain ⟨hm,physical,pair,hSource,_hCanonical,_hMatches,hA,hB,_hSec,hRich,hPoor⟩ :=
      GeneralPaperUnreplacedSourceContract.sampled_bit_epsilon model Wv Ws k epsilon hE hOne hk values v hv b hb model.rat (fun w => w) primitive A hFlag
    have hDescription := bit_description model Wv Ws A k values v hv b hb physical hSource
    rw [make_direct model.rat (fun w => w) A _ _ _ _ physical hFlag hm] at hDescription
    dsimp only at hDescription
    dsimp only
    refine ⟨.direct hm physical,hDescription,?_⟩
    simpa only [law_direct,rationalPrice,indexPrice,ite_true,Bool.false_eq_true,ite_false] using
      (And.intro hA (And.intro hB (And.intro hRich hPoor)))
  | true =>
    obtain ⟨hm,physical,pair,hSource,_hCanonical,_hMatches,hA,hB,_hSec,hRich,hPoor⟩ :=
      GeneralPaperCachedCircleSampler.original_bit_epsilon true model Wv Ws k epsilon hE hOne hk values v hv b hb model.rat (fun w => w) primitive A hFlag
    have hDescription := bit_description model Wv Ws A k values v hv b hb physical hSource
    rw [make_circle model.rat (fun w => w) A _ _ _ _ physical hFlag hm] at hDescription
    dsimp only at hDescription
    dsimp only
    refine ⟨.circle hm _ _ ,hDescription,?_⟩
    simpa only [law_circle] using (And.intro hA (And.intro hB (And.intro hRich hPoor)))


theorem arithmetic_epsilon {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      (arithmetic model k values v hv (b:ℝ)).1.description=some description ∧
      let μ := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description b true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  cases hFlag:(GeneralPaperOriginalValueReduction.run false model 1 k values).1.replaced with
  | false =>
    obtain ⟨hm,physical,pair,hSource,_hCanonical,_hMatches,hA,hB,_hSec,hRich,hPoor⟩ :=
      GeneralPaperUnreplacedSourceContract.sampled_arithmetic_epsilon model k epsilon hE hOne hk values v hv b hb (fun _ => 1) (fun _ => 1) primitive 1 hFlag
    have hDescription := arithmetic_description model k values v hv (b:ℝ) physical hSource
    rw [make_direct (fun _ => 1) (fun _ => 1) 1 _ _ _ _ physical hFlag hm] at hDescription
    dsimp only at hDescription
    dsimp only
    refine ⟨.direct hm physical,hDescription,?_⟩
    simpa only [law_direct,rationalPrice,indexPrice,ite_true,Bool.false_eq_true,ite_false] using
      (And.intro hA (And.intro hB (And.intro hRich hPoor)))
  | true =>
    obtain ⟨hm,physical,pair,hSource,_hCanonical,_hMatches,hA,hB,_hSec,hRich,hPoor⟩ :=
      GeneralPaperCachedCircleSampler.original_arithmetic_epsilon false model k epsilon hE hOne hk values v hv b hb (fun _ => 1) (fun _ => 1) primitive 1 hFlag
    have hDescription := arithmetic_description model k values v hv (b:ℝ) physical hSource
    rw [make_circle (fun _ => 1) (fun _ => 1) 1 _ _ _ _ physical hFlag hm] at hDescription
    dsimp only at hDescription
    dsimp only
    refine ⟨.circle hm _ _ ,hDescription,?_⟩
    simpa only [law_circle] using (And.intro hA (And.intro hB (And.intro hRich hPoor)))


theorem bit_pointwise {n : ℕ} (model : RationalCostModel) (Wv Ws A k : ℕ)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      (bit model Wv Ws A k values v hv b hb).1.description=some description ∧
      let μ := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description b true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) ∧
      ∀ fresh : Fin (trajectory.rowBits+(k+6)) → Bool,
        Feasible 1 (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false fresh).output.read j:ℝ)) ∧
        Feasible (b:ℝ) (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description b true fresh).output.read j:ℝ)) := by
  obtain ⟨description,hRun,hA,hB,hRich,hPoor⟩ := bit_epsilon model Wv Ws A k epsilon hE hOne hk values v hv b hb primitive
  dsimp only
  refine ⟨description,hRun,hA,hB,hRich,hPoor,?_⟩
  intro fresh
  exact ⟨every_output_feasible true primitive A _ _ _ _ _ model _ description 1 false 1 hA fresh,
    every_output_feasible true primitive A _ _ _ _ _ model _ description b true (b:ℝ) hB fresh⟩


theorem arithmetic_pointwise {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      (arithmetic model k values v hv (b:ℝ)).1.description=some description ∧
      let μ := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description b true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) ∧
      ∀ fresh : Fin (trajectory.rowBits+(k+6)) → Bool,
        Feasible 1 (fun j => ((run false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false fresh).output.read j:ℝ)) ∧
        Feasible (b:ℝ) (fun j => ((run false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description b true fresh).output.read j:ℝ)) := by
  obtain ⟨description,hRun,hA,hB,hRich,hPoor⟩ := arithmetic_epsilon model k epsilon hE hOne hk values v hv b hb primitive
  dsimp only
  refine ⟨description,hRun,hA,hB,hRich,hPoor,?_⟩
  intro fresh
  exact ⟨every_output_feasible false primitive 1 _ _ _ _ _ model _ description 1 false 1 hA fresh,
    every_output_feasible false primitive 1 _ _ _ _ _ model _ description b true (b:ℝ) hB fresh⟩

end Blotto.GeneralPaperOriginalStrategyEquilibrium
