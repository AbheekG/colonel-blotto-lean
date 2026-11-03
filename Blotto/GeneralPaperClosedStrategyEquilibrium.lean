import Blotto.GeneralPaperClosedStrategyDriver

/-! Actual epsilon preparation returns a closed sampler. Only the sampler
and fresh bits are needed by run; its stored controls/budget recover exactly
the checked source laws, with canonical continuous regrets and hard budgets. -/
namespace Blotto.GeneralPaperClosedStrategyEquilibrium
open GeneralPaperStoredStrategySampler GeneralPaperClosedStrategyDriver
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def Guarantee {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (v : Values n) (b epsilon : ℝ) (sampler : Sampler n T K) : Prop :=
  let μ := law bits primitive A model sampler false
  let ν := law bits primitive A model sampler true
  Supported 1 μ ∧ Supported b ν ∧ regret v 1 μ ν≤epsilon ∧ regret v b ν μ≤epsilon ∧
    ∀ fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool,
      Feasible 1 (fun j => ((run bits primitive A model sampler false fresh).output.read j:ℝ)) ∧
      Feasible b (fun j => ((run bits primitive A model sampler true fresh).output.read j:ℝ))

theorem of_laws {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (v : Values n) (b epsilon : ℝ) (sampler : Sampler n T K)
    (hA : Supported 1 (law bits primitive A model sampler false)) (hB : Supported b (law bits primitive A model sampler true))
    (hRich : regret v 1 (law bits primitive A model sampler false) (law bits primitive A model sampler true)≤epsilon)
    (hPoor : regret v b (law bits primitive A model sampler true) (law bits primitive A model sampler false)≤epsilon) :
    Guarantee bits primitive A model v b epsilon sampler := by
  refine ⟨hA,hB,hRich,hPoor,?_⟩
  intro fresh
  exact ⟨every_output_feasible bits primitive A model sampler false 1 hA fresh,
    every_output_feasible bits primitive A model sampler true b hB fresh⟩

theorem bit_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let prepared := (bit model Wv Ws A words values v hv b hb).1
    ∃ sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda prepared.raw.exponent).rows
      (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K,
      prepared.sampler=some sampler ∧ Guarantee true primitive A model v.values (b:ℝ) (epsilon:ℝ) sampler := by
  obtain ⟨description,hDescription,hA,hB,hRich,hPoor,_hPointwise⟩ :=
    GeneralPaperAccuracyStrategyEquilibrium.bit_epsilon model Wv Ws A words epsilon hE hOne hInput values v hv b hb primitive
  let raw := (GeneralPaperAccuracyStrategyDriver.bit model Wv Ws A words values v hv b hb).1
  let sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    ⟨raw.strategies.original.reduced,raw.budget,GeneralPaperSamplingControls.specification _
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rowBits
      raw.exponent (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent),description⟩
  dsimp only
  refine ⟨sampler,close_some (fun w => w) A raw description hDescription,?_⟩
  apply of_laws
  · exact hA
  · exact hB
  · exact hRich
  · exact hPoor

theorem arithmetic_epsilon {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    let prepared := (arithmetic model epsilon values v hv b).1
    ∃ sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda prepared.raw.exponent).rows
      (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K,
      prepared.sampler=some sampler ∧ Guarantee false primitive 1 model v.values (b:ℝ) (epsilon:ℝ) sampler := by
  obtain ⟨description,hDescription,hA,hB,hRich,hPoor,_hPointwise⟩ :=
    GeneralPaperAccuracyStrategyEquilibrium.arithmetic_epsilon model epsilon hE hOne values v hv b hb primitive
  let raw := (GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).1
  let sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    ⟨raw.strategies.original.reduced,raw.budget,GeneralPaperSamplingControls.specification _
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rowBits
      raw.exponent (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent),description⟩
  dsimp only
  refine ⟨sampler,close_some (fun _ => 1) 1 raw description hDescription,?_⟩
  apply of_laws
  · exact hA
  · exact hB
  · exact hRich
  · exact hPoor


theorem canonical_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (epsilon : ℚ)
    (hE : 0<epsilon) (hOne : epsilon<1) (suffix : List Bool)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (primitive : ℕ → ℕ) :
    ∃ prepared : Prepared n,
      (frame model Wv Ws A (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input epsilon hE)++suffix) values v hv b hb).1=
        some (prepared,suffix) ∧
      ∃ sampler : Sampler n
        (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda prepared.raw.exponent).rows
        (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K,
        prepared.sampler=some sampler ∧ Guarantee true primitive A model v.values (b:ℝ) (epsilon:ℝ) sampler := by
  obtain ⟨raw,hRaw,description,hDescription,hA,hB,hRich,hPoor,_hPointwise⟩ :=
    GeneralPaperAccuracyStrategyEquilibrium.canonical_epsilon model Wv Ws A suffix epsilon hE hOne values v hv b hb primitive
  let prepared : Prepared n := ⟨raw,(close (fun w => w) A raw).1⟩
  let sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    ⟨raw.strategies.original.reduced,raw.budget,GeneralPaperSamplingControls.specification _
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rowBits
      raw.exponent (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent),description⟩
  refine ⟨prepared,frame_some model Wv Ws A _ values v hv b hb (raw,suffix) hRaw,sampler,
    close_some (fun w => w) A raw description hDescription,?_⟩
  exact of_laws true primitive A model v.values (b:ℝ) (epsilon:ℝ) sampler hA hB hRich hPoor

end Blotto.GeneralPaperClosedStrategyEquilibrium
