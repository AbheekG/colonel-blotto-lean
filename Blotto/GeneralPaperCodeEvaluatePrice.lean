import Blotto.GeneralPaperCodeScanOperands

/-! Full candidate evaluation price. Range guards run before the decoder;
the decoded payload is wrapped once and its native counter is updated once.
-/
namespace Blotto.GeneralPaperCodeEvaluatePrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeScanExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  8388608*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))+
    4*model.rat (operandWidth a.lambda)+128*W

def arithmeticProfile (a : Alphabet) : ℕ := 16777216*(a.lambda+3)+132

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ)
    (hLo : lo≤8*a.C) (hHi : hi≤8*a.C) (hCode : code≤8*a.C) :
    (evaluate true model W a response lo hi code).2≤profile model W a := by
  have hGuards := GeneralPaperCodeScanOperands.guards_work model W a lo hi code hLo hHi hCode
  have hDecode := GeneralPaperCodeDecodePrice.bit_work model W a response code hCode
  have hAnn := GeneralPaperCodeScanOperands.evaluate_annotation model W a response code
  unfold evaluate profile
  dsimp only
  simp only [primitive,ite_true]
  split
  · dsimp only
    omega
  · dsimp only
    omega

theorem guards_unit (lo hi code : ℕ) : guards (fun _ => 1) 1 lo hi code=66 := rfl

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (response : Bool) (lo hi code : ℕ) :
    (evaluate false model 1 a response lo hi code).2≤arithmeticProfile a := by
  have hDecode := GeneralPaperCodeDecodePrice.arithmetic_work model a response code
  unfold evaluate arithmeticProfile
  dsimp only
  simp only [primitive,Bool.false_eq_true,ite_false,guards_unit]
  split
  · dsimp only
    change 66+(GeneralPaperCodeDecodeExecution.run false model 1 a response code).2+2+64≤_
    omega
  · omega

end Blotto.GeneralPaperCodeEvaluatePrice
