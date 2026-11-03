import Blotto.GeneralPaperClosedStrategyEquilibrium

/-! Genuine control-attachment work joins the complete accuracy-driven
producer. The additional arithmetic work is polylogarithmic and preserves
the real preparation rate. Global bit/space and draw prices remain open. -/
namespace Blotto.GeneralPaperClosedSamplerWork
open GeneralPaperClosedStrategyDriver GeneralPaperStoredStrategySampler
open GeneralPaperSourceWordGrowth GeneralPaperSourceRateAlgebra GeneralPaperSourceSoftBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem close_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (A : ℕ)
    (prepared : GeneralPaperAccuracyStrategyDriver.Prepared n) :
    (close primitive A prepared).2≤GeneralPaperSamplingControls.profile primitive A
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.strategies.original.reduced.m prepared.exponent).lambda prepared.exponent).rows
      prepared.exponent+128*A := by
  unfold close
  split
  · dsimp only
    omega
  · rename_i description _hDescription
    have h := store_work primitive hMono A prepared.exponent prepared.strategies.original.reduced
      (fields_positive prepared) prepared.budget description
      ⟨_,GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet prepared.strategies.original.reduced.m prepared.exponent).lambda prepared.exponent⟩
    dsimp only
    exact (Nat.add_le_add_right h (64*A)).trans_eq (by ring)

def extraPrice (m k : ℕ) : ℕ := GeneralPaperSamplingControls.profile (fun _ => 1) 1
  (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows k+256

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) :
    let raw := (GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).1
    (arithmetic model epsilon values v hv b).2≤(GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).2+
      extraPrice raw.strategies.original.reduced.m raw.exponent := by
  have h := close_work (fun _ => 1) (fun _ _ _ => le_rfl) 1
    (GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).1
  dsimp only [arithmetic,extraPrice]
  exact (Nat.add_le_add_right (Nat.add_le_add_left h _) 128).trans_eq (by ring)

theorem bit_work {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) :
    let raw := (GeneralPaperAccuracyStrategyDriver.bit model Wv Ws A words values v hv b hb).1
    (bit model Wv Ws A words values v hv b hb).2≤(GeneralPaperAccuracyStrategyDriver.bit model Wv Ws A words values v hv b hb).2+
      GeneralPaperSamplingControls.profile (fun w => w) A
        (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows raw.exponent+256*A := by
  have h := close_work (fun w => w) (fun _ _ h => h) A
    (GeneralPaperAccuracyStrategyDriver.bit model Wv Ws A words values v hv b hb).1
  dsimp only [bit]
  exact (Nat.add_le_add_right (Nat.add_le_add_left h _) (128*A)).trans_eq (by ring)

theorem extra_rate : Rated (fun x => extraPrice x.m x.k) 0 0 0 := by
  have hw := GeneralPaperSourceRateAlgebra.rows_word
  unfold extraPrice GeneralPaperSamplingControls.profile GeneralPaperNaturalPrimitivePrice.binary
  change Rated _ 0 0 0
  source_space

theorem extra_core_time : ∃ A e : ℕ,∀ x : Input,extraPrice x.m x.k≤A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e := by
  apply GeneralPaperSourceCoreLogBound.remove_unused_height (weaken extra_rate (by decide) (by decide) (by decide))
  · intro x
    rfl
  · intro x
    rfl

theorem real_input_time (model : RationalCostModel) :
    ∃ A e : ℕ,∀ {n : ℕ} (epsilon : ℚ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ),0<b ∧ b<1 →
      let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
      let x := GeneralPaperOriginalSourceValuePreparation.input
        (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1 k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
      (arithmetic model epsilon values v hv b).2≤A*(n+1+monomial 2 0 5 x)*(GeneralPaperOriginalSourceValueContract.inputLog n k 0)^e := by
  obtain ⟨As,es,hSource⟩ := GeneralPaperAccuracyStrategyDriver.real_input_time model
  obtain ⟨Ac,ec,hExtra⟩ := extra_core_time
  refine ⟨As+Ac*4^ec,es+ec+1,?_⟩
  intro n epsilon values v hv b hb
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  let x := GeneralPaperOriginalSourceValuePreparation.input
    (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1 k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
  let R := n+1+monomial 2 0 5 x
  let L := GeneralPaperOriginalSourceValueContract.inputLog n k 0
  let D := es+ec+1
  have hL : 1≤L := GeneralPaperOriginalSourceValueContract.input_log_positive n k 0
  have hM : monomial 2 0 5 x≤R := by dsimp only [R];omega
  have hEs : L^es≤L^D := Nat.pow_le_pow_right hL (by dsimp only [D];omega)
  have hEc : L^ec≤L^D := Nat.pow_le_pow_right hL (by dsimp only [D];omega)
  have hLog : GeneralPaperSourceCoreLogBound.coreLog x≤4*L :=
    (GeneralPaperOriginalSourceValueContract.original_log_bound false model 1 k 2 values v hv (1/2)
      (by norm_num) (by norm_num [RationalHeight])).2
  have hS : (GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).2≤As*R*L^D :=
    (hSource epsilon values v hv b hb).trans (Nat.mul_le_mul_left _ hEs)
  have hC : extraPrice (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k≤Ac*4^ec*R*L^D := by
    calc
      _≤Ac*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^ec := hExtra x
      _≤Ac*monomial 2 0 5 x*(4*L)^ec := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog ec)
      _=Ac*4^ec*monomial 2 0 5 x*L^ec := by rw [mul_pow];ring
      _≤Ac*4^ec*R*L^D := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hEc
  have hNative := arithmetic_work model epsilon values v hv b
  change (arithmetic model epsilon values v hv b).2≤(GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).2+
    extraPrice (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k at hNative
  exact hNative.trans (by
    change _≤(As+Ac*4^ec)*R*L^D
    nlinarith only [hS,hC])

end Blotto.GeneralPaperClosedSamplerWork
