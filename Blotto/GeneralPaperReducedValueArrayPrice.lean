import Blotto.GeneralPaperReducedValuesDriver

/-! Literal native reduced-value array prices. All rational operands are
short returned integers or their fractions; width bounds are erased analysis.
The once-only representative division is charged separately from references. -/
namespace Blotto.GeneralPaperReducedValueArrayPrice
open GeneralPaperReducedValueArray GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open GeneralPaperDecodeBucketExecution (primitive)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def width (Q R : ℕ) : ℕ := 64+16*(binaryWordWidth Q+binaryWordWidth R)

theorem cast_width (w Q R : ℕ) (hw : w≤Q) : rationalWordWidth (w:ℚ)≤width Q R := by
  have h := rationalWordWidth_of_height ((GeneralPaperBasisDivideBits.nat_height w).mono (binaryWordWidth_mono hw))
  unfold width
  omega

theorem ratio_width (w Q R : ℕ) (hw : w≤Q) : rationalWordWidth ((w:ℚ)/Q)≤width Q R := by
  have h := rationalWordWidth_of_height (((GeneralPaperBasisDivideBits.nat_height w).mono (binaryWordWidth_mono hw)).div
    (GeneralPaperBasisDivideBits.nat_height Q))
  unfold width
  omega

theorem denominator_width (Q R : ℕ) : rationalWordWidth ((Q*R:ℕ):ℚ)≤width Q R := by
  have h := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height (Q*R))
  have hm := binaryWordWidth_mul Q R
  unfold width
  omega

theorem representative_width (L Q R : ℕ) (hL : L≤Q) : rationalWordWidth ((L:ℚ)/(Q*R:ℕ))≤width Q R := by
  have h := rationalWordWidth_of_height (((GeneralPaperBasisDivideBits.nat_height L).mono (binaryWordWidth_mono hL)).div
    (GeneralPaperBasisDivideBits.nat_height (Q*R)))
  have hm := binaryWordWidth_mul Q R
  unfold width
  omega

theorem control_word (W N i : ℕ) (hi : i≤N) : 1+binaryWordWidth i≤arrayWord W N := by
  have h := binaryWordWidth_mono (by omega : i≤N+1)
  unfold arrayWord
  omega

theorem coordinate_bit_work {n : ℕ} (model : RationalCostModel) (W Q R : ℕ) (rep : ℚ)
    (weights : FixedArrayTable n ℕ) (hw : ∀ j,weights.read j≤Q) (heavy : Array (Fin n)) (j : Fin (heavy.size+R)) :
    (coordinate true model (arrayWord W (n+heavy.size+R)) Q rep weights heavy j).2≤
      3*model.rat (width Q R)+64*arrayWord W (n+heavy.size+R) := by
  have hc := GeneralPaperIntegerWordPrice.compare_le (fun w => w) (fun _ _ h => h) j.val heavy.size
    (arrayWord W (n+heavy.size+R)) (control_word W _ _ (by omega)) (control_word W _ _ (by omega))
  unfold coordinate
  simp only [primitive,index,ite_true]
  split_ifs with hj
  · have hCast := model.monotone (cast_width _ Q R (hw heavy[j.val]))
    have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
      (weights.read heavy[j.val]) Q (width Q R) (cast_width _ Q R (hw _)) (cast_width Q Q R le_rfl)
      (ratio_width _ Q R (hw _))
    nlinarith only [hc,hCast,hDiv]
  · nlinarith only [hc]

theorem replaced_bit_work {n : ℕ} (model : RationalCostModel) (W Q R L : ℕ)
    (weights : FixedArrayTable n ℕ) (hw : ∀ j,weights.read j≤Q) (heavy : Array (Fin n)) (hL : L≤Q) :
    (replaced true model W Q R L weights heavy).2≤
      (heavy.size+R)*(3*model.rat (width Q R)+64*arrayWord W (n+heavy.size+R))+
      44*(heavy.size+R+1)*arrayWord W (n+heavy.size+R)+7*model.rat (width Q R)+128*arrayWord W (n+heavy.size+R) := by
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W (n+heavy.size+R)
  have hArray := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W (n+heavy.size+R))
    (3*model.rat (width Q R)+64*arrayWord W (n+heavy.size+R))
    (coordinate true model (arrayWord W (n+heavy.size+R)) Q ((L:ℚ)/(Q*R:ℕ)) weights heavy)
    hA (fun i hi => GeneralPaperSummaryArrayControls.array_index W _ i (by omega))
    (coordinate_bit_work model W Q R _ weights hw heavy)
  have hWord := binaryWordWidth_mul Q R
  have hMul := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) Q R
    (width Q R) (by unfold width; omega) (by unfold width; omega) (by unfold width; omega)
  have hQ := model.monotone (cast_width Q Q R le_rfl)
  have hD := model.monotone (denominator_width Q R)
  have hL' := model.monotone (cast_width L Q R hL)
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) L (Q*R:ℕ)
    (width Q R) (cast_width L Q R hL) (denominator_width Q R) (representative_width L Q R hL)
  unfold replaced
  dsimp only
  simp only [primitive,index,address,ite_true]
  nlinarith only [hArray,hMul,hQ,hD,hL',hDiv]

theorem identity_bit_work {n : ℕ} (model : RationalCostModel) (W Q : ℕ)
    (weights : FixedArrayTable n ℕ) (hw : ∀ j,weights.read j≤Q) :
    (identity true model W Q weights).2≤n*(3*model.rat (width Q 1)+32*arrayWord W n)+
      44*(n+1)*arrayWord W n+model.rat (width Q 1)+128*arrayWord W n := by
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
  have hArray := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n)
    (3*model.rat (width Q 1)+32*arrayWord W n)
    (fun j : Fin n => ((weights.read j:ℚ)/(Q:ℚ),model.rat (rationalWordWidth (weights.read j:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (weights.read j) Q+32*arrayWord W n))
    hA (GeneralPaperSummaryArrayControls.array_index W n) (by
      intro j
      have hCast := model.monotone (cast_width _ Q 1 (hw j))
      have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (weights.read j) Q
        (width Q 1) (cast_width _ Q 1 (hw j)) (cast_width Q Q 1 le_rfl) (ratio_width _ Q 1 (hw j))
      dsimp only
      nlinarith only [hCast,hDiv])
  have hQ := model.monotone (cast_width Q Q 1 le_rfl)
  unfold identity
  dsimp only
  simp only [primitive,index,address,ite_true]
  nlinarith only [hArray,hQ]

theorem coordinate_arithmetic_work {n : ℕ} (model : RationalCostModel) (Q R : ℕ) (rep : ℚ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) (j : Fin (heavy.size+R)) :
    (coordinate false model 1 Q rep weights heavy j).2≤36 := by
  unfold coordinate
  simp only [primitive,index,Bool.false_eq_true,ite_false,GeneralPaperIntegerWordPrice.compare,
    GeneralPaperRationalPrimitivePrice.binary,Nat.mul_one]
  split_ifs <;> norm_num

theorem replaced_arithmetic_work {n : ℕ} (model : RationalCostModel) (Q R L : ℕ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) :
    (replaced false model 1 Q R L weights heavy).2≤80*(heavy.size+R)+179 := by
  have hArray := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 36
    (coordinate false model 1 Q ((L:ℚ)/(Q*R:ℕ)) weights heavy) (by decide) (fun _ _ => le_rfl)
    (coordinate_arithmetic_work model Q R _ weights heavy)
  unfold replaced
  dsimp only
  simp only [primitive,index,address,Bool.false_eq_true,ite_false,GeneralPaperNaturalPrimitivePrice.binary,
    GeneralPaperRationalPrimitivePrice.binary,Nat.mul_one]
  nlinarith only [hArray]

theorem identity_arithmetic_work {n : ℕ} (model : RationalCostModel) (Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (identity false model 1 Q weights).2≤79*n+173 := by
  have hArray := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 35
    (fun j : Fin n => ((weights.read j:ℚ)/(Q:ℚ),35)) (by decide) (fun _ _ => le_rfl) (fun _ => le_rfl)
  unfold identity
  dsimp only
  simp only [primitive,index,address,Bool.false_eq_true,ite_false,GeneralPaperRationalPrimitivePrice.binary,Nat.mul_one]
  nlinarith only [hArray]

end Blotto.GeneralPaperReducedValueArrayPrice
