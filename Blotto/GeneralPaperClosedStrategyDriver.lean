import Blotto.GeneralPaperStoredStrategySampler

/-! Attach stored sampler controls to the actual accuracy-driven return.
Only retained array descriptor metadata, a short dyadic count constructor
and new fixed parents execute. The source/accuracy/description is not rerun. -/
namespace Blotto.GeneralPaperClosedStrategyDriver
open GeneralPaperStoredStrategySampler
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem fields_positive {n : ℕ} (prepared : GeneralPaperAccuracyStrategyDriver.Prepared n) :
    0<prepared.strategies.original.reduced.m := by
  by_contra h
  have hz : prepared.strategies.original.reduced.m=0 := by omega
  have hs := prepared.strategies.original.weight_sum
  have he : ∑ j:Fin prepared.strategies.original.reduced.m,prepared.strategies.original.weights.read j=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    omega
  rw [he] at hs
  have hp := prepared.strategies.original.Qv_positive
  omega

structure Prepared (n : ℕ) where
  raw : GeneralPaperAccuracyStrategyDriver.Prepared n
  sampler : Option (Sampler n
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
    (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K)

def close {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (prepared : GeneralPaperAccuracyStrategyDriver.Prepared n) :
    Option (Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.strategies.original.reduced.m prepared.exponent).lambda prepared.exponent).rows
      (GeneralPaperProxyParameters.prepare prepared.strategies.original.reduced.m prepared.exponent).K)×ℕ :=
  match prepared.strategies.description with
  | none => (none,64*A)
  | some description =>
    let stored := store primitive A prepared.exponent prepared.strategies.original.reduced (fields_positive prepared) prepared.budget description
      ⟨_,GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet prepared.strategies.original.reduced.m prepared.exponent).lambda prepared.exponent⟩
    (some stored.1,stored.2+64*A)

theorem close_some {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (prepared : GeneralPaperAccuracyStrategyDriver.Prepared n)
    (description : GeneralPaperStrategyDescription.Description prepared.strategies.original.reduced
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.strategies.original.reduced.m prepared.exponent).lambda prepared.exponent).rows
      (GeneralPaperProxyParameters.prepare prepared.strategies.original.reduced.m prepared.exponent).K)
    (hDescription : prepared.strategies.description=some description) :
    (close primitive A prepared).1=some
      (⟨prepared.strategies.original.reduced,prepared.budget,
        GeneralPaperSamplingControls.specification _
          (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.strategies.original.reduced.m prepared.exponent).lambda prepared.exponent).rowBits
          prepared.exponent (GeneralPaperTrajectoryParameters.rows_power
            (GeneralPaperProxyParameters.alphabet prepared.strategies.original.reduced.m prepared.exponent).lambda prepared.exponent),description⟩) := by
  dsimp only [close]
  rw [hDescription]
  dsimp only
  rw [store_data]

def bit {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : Prepared n×ℕ :=
  let raw := GeneralPaperAccuracyStrategyDriver.bit model Wv Ws A words values v hv b hb
  let stored := close (fun w => w) A raw.1
  (⟨raw.1,stored.1⟩,raw.2+stored.2+128*A)

noncomputable def arithmetic {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) : Prepared n×ℕ :=
  let raw := GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b
  let stored := close (fun _ => 1) 1 raw.1
  (⟨raw.1,stored.1⟩,raw.2+stored.2+128)

def frame {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (input : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : Option (Prepared n×List Bool)×ℕ :=
  let raw := GeneralPaperAccuracyStrategyDriver.frame model Wv Ws A input values v hv b hb
  match raw.1 with
  | none => (none,raw.2+64*A)
  | some parsed =>
    let stored := close (fun w => w) A parsed.1
    (some (⟨parsed.1,stored.1⟩,parsed.2),raw.2+stored.2+128*A)

theorem bit_raw {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) :
    (bit model Wv Ws A words values v hv b hb).1.raw=(GeneralPaperAccuracyStrategyDriver.bit model Wv Ws A words values v hv b hb).1 := rfl

theorem arithmetic_raw {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) :
    (arithmetic model epsilon values v hv b).1.raw=(GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).1 := rfl

theorem frame_some {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (input : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (parsed : GeneralPaperAccuracyStrategyDriver.Prepared n×List Bool)
    (hRaw : (GeneralPaperAccuracyStrategyDriver.frame model Wv Ws A input values v hv b hb).1=some parsed) :
    (frame model Wv Ws A input values v hv b hb).1=some (⟨parsed.1,(close (fun w => w) A parsed.1).1⟩,parsed.2) := by
  simp only [frame,hRaw]

end Blotto.GeneralPaperClosedStrategyDriver
