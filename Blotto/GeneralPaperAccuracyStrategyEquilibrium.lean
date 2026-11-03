import Blotto.GeneralPaperAccuracyStrategyDriver

/-! Actual rational-accuracy preparation returns native descriptions with
original-game epsilon guarantees. The exponent is computed by the producer,
not supplied with a caller-side accuracy identity. Pointwise budgets hold
for every fresh-bit string and the original budget is retained once. -/
namespace Blotto.GeneralPaperAccuracyStrategyEquilibrium
open GeneralPaperStrategyDescription GeneralPaperAccuracyStrategyDriver
open GeneralPaperOriginalDrawEquilibrium GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem bit_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let prepared := (bit model Wv Ws A words values v hv b hb).1
    let k := prepared.exponent
    let o := prepared.strategies.original.reduced
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.strategies.description=some description ∧
      let μ := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) ∧
      ∀ fresh : Fin (trajectory.rowBits+(k+6)) → Bool,
        Feasible 1 (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false fresh).output.read j:ℝ)) ∧
        Feasible (b:ℝ) (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true fresh).output.read j:ℝ)) := by
  exact GeneralPaperOriginalStrategyEquilibrium.bit_pointwise model Wv Ws A
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) A words).1 epsilon hE hOne
    (GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) A words epsilon hInput) values v hv b hb primitive

theorem arithmetic_epsilon {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let prepared := (arithmetic model epsilon values v hv b).1
    let k := prepared.exponent
    let o := prepared.strategies.original.reduced
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.strategies.description=some description ∧
      let μ := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) ∧
      ∀ fresh : Fin (trajectory.rowBits+(k+6)) → Bool,
        Feasible 1 (fun j => ((run false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false fresh).output.read j:ℝ)) ∧
        Feasible (b:ℝ) (fun j => ((run false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true fresh).output.read j:ℝ)) := by
  exact GeneralPaperOriginalStrategyEquilibrium.arithmetic_pointwise model (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
    epsilon hE hOne rfl values v hv b hb primitive


theorem encoded_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (accuracy : BinaryAccuracyInput) (suffix : List Bool)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hInput : epsilon=(accuracy.numerator:ℚ)/accuracy.denominator)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    ∃ prepared : Prepared n,
      (frame model Wv Ws A (BinaryAccuracyFrame.encode accuracy++suffix) values v hv b hb).1=some (prepared,suffix) ∧
    let k := prepared.exponent
    let o := prepared.strategies.original.reduced
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.strategies.description=some description ∧
      let μ := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) ∧
      ∀ fresh : Fin (trajectory.rowBits+(k+6)) → Bool,
        Feasible 1 (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false fresh).output.read j:ℝ)) ∧
        Feasible (b:ℝ) (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true fresh).output.read j:ℝ)) := by
  obtain ⟨parsed,hRead,hNumeric⟩ := GeneralPaperBinaryAccuracy.read_complete (fun w => w) A accuracy suffix
  have hn : parsed.words.numerator.value=accuracy.numerator := congrArg BinaryAccuracyInput.numerator hNumeric
  have hd : parsed.words.denominator.value=accuracy.denominator := congrArg BinaryAccuracyInput.denominator hNumeric
  have hParsed : epsilon=(parsed.words.numerator.value:ℚ)/parsed.words.denominator.value := by rw [hn,hd];exact hInput
  have hk := GeneralPaperBinaryAccuracy.read_exponent (fun w => w) A _ (parsed,suffix) hRead epsilon hParsed
  refine ⟨(bitFromExponent model Wv Ws A parsed.exponent values v hv b hb).1,
    (frame_some model Wv Ws A _ values v hv b hb (parsed,suffix) hRead).1,?_⟩
  exact GeneralPaperOriginalStrategyEquilibrium.bit_pointwise model Wv Ws A parsed.exponent epsilon hE hOne hk values v hv b hb primitive


theorem canonical_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (suffix : List Bool)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    ∃ prepared : Prepared n,
      (frame model Wv Ws A (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input epsilon hE)++suffix) values v hv b hb).1=some (prepared,suffix) ∧
    let k := prepared.exponent
    let o := prepared.strategies.original.reduced
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.strategies.description=some description ∧
      let μ := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) ∧
      ∀ fresh : Fin (trajectory.rowBits+(k+6)) → Bool,
        Feasible 1 (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false fresh).output.read j:ℝ)) ∧
        Feasible (b:ℝ) (fun j => ((run true primitive A trajectory.rowBits (k+6) (count k) hRows hShift model o description prepared.budget true fresh).output.read j:ℝ)) := by
  exact encoded_epsilon model Wv Ws A (GeneralPaperBinaryAccuracy.input epsilon hE) suffix epsilon hE hOne
    (GeneralPaperBinaryAccuracy.input_value epsilon hE).symm values v hv b hb primitive

end Blotto.GeneralPaperAccuracyStrategyEquilibrium
