import Blotto.GeneralPaperOriginalSourceValuePrice

/-! Actual original-value-to-physical-pair producers. One value preparation
feeds one arithmetic/fast-bit pair call. The returned original record and
physical columns are retained; all size/contract facts are erased. -/
namespace Blotto.GeneralPaperOriginalSourceValueDriver
open GeneralPaperOriginalSourceValuePreparation GeneralPaperOriginalDrawEquilibrium
open GeneralPaperSourceWordGrowth
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

structure Prepared (n k : ℕ) where
  original : Output n
  physical : Option (Columns (GeneralPaperTrajectoryParameters.prepare
    (GeneralPaperProxyParameters.alphabet original.reduced.m k).lambda k).rows original.reduced.m
    (GeneralPaperProxyParameters.prepare original.reduced.m k).K)

noncomputable def arithmetic {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) : Prepared n k×ℕ :=
  let prepared := GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv
  let pair := GeneralPaperArithmeticSourcePairDriver.run model k prepared.1.Qv prepared.1.Qv_positive
    prepared.1.weights prepared.1.weights_positive prepared.1.weight_sum b
  (⟨prepared.1,pair.1⟩,prepared.2+pair.2+128)

def bit {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) : Prepared n k×ℕ :=
  let prepared := GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv
  let pair := GeneralPaperFastRationalPairDriver.run model Ws Ws k prepared.1.Qv prepared.1.Qv_positive
    prepared.1.weights prepared.1.weights_positive prepared.1.weight_sum b hb
  (⟨prepared.1,pair.1⟩,prepared.2+pair.2+128*Ws)

theorem arithmetic_original {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) :
    (arithmetic model k values v hv b).1.original=(GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1 := rfl

theorem bit_original {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    (bit model Wv Ws k values v hv b hb).1.original=(GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1 := rfl

theorem arithmetic_return {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    ∃ physical pair,(arithmetic model k values v hv b).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run false model 1 k o.reduced.values redValues (fun _ => rfl) b=some pair ∧
      Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k o.Qv o.Qv_positive o.weights o.weights_positive o.weight_sum b pair := by
  dsimp only
  let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
  have hm := (count_bounds false model 1 k values v hv).1
  obtain ⟨physical,pair,hNative,hSource,hMatches,hContract⟩ := GeneralPaperArithmeticSourcePairDriver.actual_return model k
    o.Qv hm o.Qv_positive o.weights o.weights_positive o.weight_sum b hb
  exact ⟨physical,pair,hNative,hSource,hMatches,hContract⟩

theorem bit_return {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    ∃ physical pair,(bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run true model Wv k o.reduced.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧
      Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k o.Qv o.Qv_positive o.weights o.weights_positive o.weight_sum (b:ℝ) pair := by
  dsimp only
  let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
  have hm := (count_bounds true model Wv k values v hv).1
  obtain ⟨physical,pair,hNative,hSource,hMatches,hContract⟩ := GeneralPaperFastDriverReferenceContract.actual_return model Ws k
    o.Qv o.Qv_positive o.weights o.weights_positive o.weight_sum b hm hb
  exact ⟨physical,pair,hNative,hSource,hMatches,hContract⟩

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
    (arithmetic model k values v hv b).2≤GeneralPaperOriginalSourceValuePrice.arithmeticPrice n k+
      GeneralPaperArithmeticDriverWork.price o.reduced.m k o.Qv+128 := by
  dsimp only
  let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
  have hPrep := GeneralPaperOriginalSourceValuePrice.arithmetic_work model k values v hv
  have hm := (count_bounds false model 1 k values v hv).1
  have hPair := GeneralPaperArithmeticDriverWork.work model k o.Qv hm o.Qv_positive o.weights o.weights_positive o.weight_sum b hb
  exact Nat.add_le_add_right (Nat.add_le_add hPrep hPair) 128

theorem native_bit_work {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (Wv k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
    let x := input o k B b hb hB
    let Ws := GeneralPaperFastDriverReference.width C d x
    (bit model Wv Ws k values v hv b hb).2≤GeneralPaperOriginalSourceValuePrice.bitPrice model Wv k values+
      GeneralPaperFastWholeDriverStorage.price model C d Ws x.m x.k x.Qv x.B+128*Ws := by
  dsimp only
  let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
  let x := input o k B b hb hB
  have hPrep := GeneralPaperOriginalSourceValuePrice.bit_work model Wv k values v hv
  have hPair := GeneralPaperFastDriverSharpWork.native_price hg x (count_bounds true model Wv k values v hv).1 o.Qv_positive o.weights_positive
  exact Nat.add_le_add_right (Nat.add_le_add hPrep hPair) _

theorem real_source_time (model : RationalCostModel) :
    ∃ A e : ℕ,∀ {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
      (b : ℝ),0<b ∧ b<1 →
      let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
      let x := input o k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
      (arithmetic model k values v hv b).2≤GeneralPaperOriginalSourceValuePrice.arithmeticPrice n k+
        A*GeneralPaperSourceRateAlgebra.monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e+128 := by
  obtain ⟨A,e,h⟩ := GeneralPaperArithmeticDriverSharpTime.real_time model 18
  refine ⟨A,e,?_⟩
  intro n k values v hv b hb
  let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
  let x := input o k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
  have hPair := h x (count_bounds false model 1 k values v hv).1 o.Qv_positive o.weights_positive
    (field_cap false model 1 k 2 values v hv (1/2) (by norm_num) (by norm_num [RationalHeight])) b hb
  exact Nat.add_le_add_right (Nat.add_le_add (GeneralPaperOriginalSourceValuePrice.arithmetic_work model k values v hv) hPair) 128

end Blotto.GeneralPaperOriginalSourceValueDriver
