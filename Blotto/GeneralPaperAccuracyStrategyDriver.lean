import Blotto.GeneralPaperBinaryAccuracy

/-! Rational accuracy is an actual input to both producer models. The bit
path reads Boolean words and the arithmetic path uses the checked rational
doubling routine. Both retain the resulting exponent and original budget;
source and description construction execute once at that exponent. -/
namespace Blotto.GeneralPaperAccuracyStrategyDriver
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

structure Prepared (n : ℕ) where
  exponent : ℕ
  budget : ℚ
  strategies : GeneralPaperOriginalStrategyDriver.Prepared n exponent

def bitFromExponent {n : ℕ} (model : RationalCostModel) (Wv Ws A k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : Prepared n×ℕ :=
  let core := GeneralPaperOriginalStrategyDriver.bit model Wv Ws A k values v hv b hb
  (⟨k,b,core.1⟩,core.2+64*A)

def bit {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : Prepared n×ℕ :=
  let accuracy := GeneralPaperBinaryAccuracy.prepare (fun w => w) A words
  let core := bitFromExponent model Wv Ws A accuracy.1 values v hv b hb
  (core.1,accuracy.2+core.2+64*A)

noncomputable def arithmetic {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) : Prepared n×ℕ :=
  let accuracy := GeneralPaperDyadicAccuracy.prepare epsilon
  let core := GeneralPaperOriginalStrategyDriver.arithmetic model accuracy.exponent values v hv (b:ℝ)
  (⟨accuracy.exponent,b,core.1⟩,accuracy.work+core.2+128)

def frame {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (input : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : Option (Prepared n×List Bool)×ℕ :=
  let accuracy := GeneralPaperBinaryAccuracy.read (fun w => w) A input
  match accuracy.1 with
  | none => (none,accuracy.2+64*A)
  | some parsed =>
    let core := bitFromExponent model Wv Ws A parsed.1.exponent values v hv b hb
    (some (core.1,parsed.2),accuracy.2+core.2+64*A)

theorem bit_exponent {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) :
    (bit model Wv Ws A words values v hv b hb).1.exponent=(GeneralPaperBinaryAccuracy.prepare (fun w => w) A words).1 := rfl

theorem bit_budget {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) :
    (bit model Wv Ws A words values v hv b hb).1.budget=b := rfl

theorem arithmetic_exponent {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) :
    (arithmetic model epsilon values v hv b).1.exponent=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent := rfl

theorem arithmetic_budget {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) :
    (arithmetic model epsilon values v hv b).1.budget=b := rfl

theorem bit_work {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (hCap : 1+binaryWordWidth (words.numerator.width+words.denominator.width+1)≤A) :
    (bit model Wv Ws A words values v hv b hb).2≤128*(words.numerator.width+words.denominator.width+1)*A+
      (GeneralPaperOriginalStrategyDriver.bit model Wv Ws A (GeneralPaperBinaryAccuracy.prepare (fun w => w) A words).1 values v hv b hb).2+128*A := by
  have h := GeneralPaperBinaryAccuracy.prepare_work (fun w => w) (fun _ _ h => h) A words hCap
  dsimp only [bit,bitFromExponent]
  omega

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (epsilon : ℚ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) :
    (arithmetic model epsilon values v hv b).2≤12*(GeneralPaperDyadicAccuracy.prepare epsilon).exponent+
      (GeneralPaperOriginalStrategyDriver.arithmetic model (GeneralPaperDyadicAccuracy.prepare epsilon).exponent values v hv (b:ℝ)).2+138 := by
  dsimp only [arithmetic]
  rw [GeneralPaperDyadicAccuracy.prepare_work_exact]
  omega

theorem frame_some {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (input : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) A input).1=some parsed) :
    (frame model Wv Ws A input values v hv b hb).1=
      some ((bitFromExponent model Wv Ws A parsed.1.exponent values v hv b hb).1,parsed.2) ∧
    (frame model Wv Ws A input values v hv b hb).2=(GeneralPaperBinaryAccuracy.read (fun w => w) A input).2+
      (GeneralPaperOriginalStrategyDriver.bit model Wv Ws A parsed.1.exponent values v hv b hb).2+128*A := by
  simp only [frame,hRead]
  constructor
  · trivial
  · dsimp only [bitFromExponent]
    ring

theorem frame_work {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (input : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) A input).1=some parsed)
    (hCap : 1+binaryWordWidth (input.length+1)≤A) :
    (frame model Wv Ws A input values v hv b hb).2≤256*(input.length+1)*A+
      (GeneralPaperOriginalStrategyDriver.bit model Wv Ws A parsed.1.exponent values v hv b hb).2+128*A := by
  rw [(frame_some model Wv Ws A input values v hv b hb parsed hRead).2]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (GeneralPaperBinaryAccuracy.read_work (fun w => w) (fun _ _ h => h) A input hCap) _) _


theorem real_input_time (model : RationalCostModel) :
    ∃ A e : ℕ,∀ {n : ℕ} (epsilon : ℚ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ),0<b ∧ b<1 →
      let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
      let x := GeneralPaperOriginalSourceValuePreparation.input
        (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1 k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
      (arithmetic model epsilon values v hv b).2≤A*(n+1+GeneralPaperSourceRateAlgebra.monomial 2 0 5 x)*
        (GeneralPaperOriginalSourceValueContract.inputLog n k 0)^e := by
  obtain ⟨A,e,hTime⟩ := GeneralPaperStrategyPreparationWork.real_input_time model
  refine ⟨A+150,e+1,?_⟩
  intro n epsilon values v hv b hb
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  let x := GeneralPaperOriginalSourceValuePreparation.input
    (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1 k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
  let R := n+1+GeneralPaperSourceRateAlgebra.monomial 2 0 5 x
  let L := GeneralPaperOriginalSourceValueContract.inputLog n k 0
  have hL : 1≤L := GeneralPaperOriginalSourceValueContract.input_log_positive n k 0
  have hk : k≤L := by unfold L GeneralPaperOriginalSourceValueContract.inputLog;omega
  have hR : 1≤R := by dsimp only [R];omega
  have hPow : L^e≤L^(e+1) := Nat.pow_le_pow_right hL (by omega)
  have hOld : (GeneralPaperOriginalStrategyDriver.arithmetic model k values v hv (b:ℝ)).2≤A*R*L^(e+1) :=
    (hTime k values v hv (b:ℝ) (by exact_mod_cast hb)).trans (Nat.mul_le_mul_left _ hPow)
  have hLP : L≤L^(e+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hL (show 1≤e+1 by omega)
  have hRP : L≤R*L^(e+1) := hLP.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (L^(e+1)) hR)
  have hParent : 12*k+138≤150*R*L^(e+1) := by nlinarith only [hk,hRP,hL]
  exact (arithmetic_work model epsilon values v hv b).trans (by
    change _≤(A+150)*R*L^(e+1)
    nlinarith only [hOld,hParent])

end Blotto.GeneralPaperAccuracyStrategyDriver
