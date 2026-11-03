import Blotto.GeneralPaperCodeDecodeExecution

/-! Complete literal decoder price, with exact native choices and counters.
Input caps are derived by surrounding cell/point constructors; the decoder
itself performs tail rejection before calling either constructed subroutine.
-/
namespace Blotto.GeneralPaperCodeDecodePrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeDecodeExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem control_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hCode : code≤8*a.C) :
    GeneralPaperCodeDecodeExecution.control model.rat W a code≤3*model.rat (operandWidth a.lambda)+64*W := by
  have hc := a.scalePositive
  have hWord := code_word a (8*a.C) (Nat.le_refl _)
  have hLimit := (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) 4 a.C (8*a.C)
    (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (model.monotone hWord))
  have hTest := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone code (4*a.C) (operandWidth a.lambda)
    (code_word a code hCode) (code_word a (4*a.C) (by omega))
  unfold GeneralPaperCodeDecodeExecution.control
  omega

theorem additions_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) :
    let split := GeneralPaperCodeSplitExecution.run true model W code a.lambda
    let found := GeneralPaperDecodeBucketExecution.run true model W a response split.1.bucket split.1.slot
    additions model.rat split.1.work found.1.work≤4*model.rat (operandWidth a.lambda) := by
  let split := GeneralPaperCodeSplitExecution.run true model W code a.lambda
  let found := GeneralPaperDecodeBucketExecution.run true model W a response split.1.bucket split.1.slot
  have hs : split.1.work≤14*a.lambda+42 := by
    dsimp only [split]
    rw [GeneralPaperCodeSplitExecution.data]
    exact GeneralPaperCodeSplit.run_work code a.lambda
  have hb := GeneralPaperDecodeBucketPrice.native_work true model W a response split.1.bucket split.1.slot
  change found.1.work≤170*a.lambda+418 at hb
  change additions model.rat split.1.work found.1.work≤_
  have hFirst := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b) split.1.work found.1.work
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  have hLast := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b) (split.1.work+found.1.work) 16
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  unfold additions
  omega

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) (hCode : code≤8*a.C) :
    (run true model W a response code).2≤8388608*(a.lambda+3)*
      (controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  let P := model.rat (operandWidth a.lambda)
  let F := controlWord W a.lambda+P
  have hControl := control_work model W a code hCode
  change _≤3*P+64*W at hControl
  have hWF : W≤F := by dsimp [F,controlWord]; omega
  have hPF : P≤F := by dsimp only [F]; omega
  change _≤8388608*(a.lambda+3)*F
  unfold run
  dsimp only
  simp only [primitive,ite_true]
  split
  · rename_i hRange
    have hSplit := GeneralPaperCodeSplitPrice.bit_work model W a code hRange
    have hSpec := GeneralPaperCodeSplitPrice.specification true model W a code hRange
    have hBucket := GeneralPaperCodeSplitPrice.bucket_bound true model W a code hRange
    have hFound := GeneralPaperDecodeBucketPrice.bit_work model W a response
      (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1.bucket
      (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1.slot hBucket hSpec.2
    have hAdds := additions_work model W a response code
    change _≤4096*(a.lambda+3)*F at hSplit
    change _≤4194304*(a.lambda+3)*F at hFound
    change _≤4*P at hAdds
    dsimp only
    nlinarith only [hControl,hSplit,hFound,hAdds,hWF,hPF,Nat.zero_le (a.lambda*F)]
  · dsimp only
    nlinarith only [hControl,hWF,hPF,Nat.zero_le (a.lambda*F)]

theorem control_unit (a : Alphabet) (code : ℕ) : GeneralPaperCodeDecodeExecution.control (fun _ => 1) 1 a code=67 := rfl

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (response : Bool) (code : ℕ) :
    (run false model 1 a response code).2≤16777216*(a.lambda+3) := by
  unfold run
  dsimp only
  simp only [primitive,Bool.false_eq_true,ite_false,control_unit]
  split
  · have hSplit := GeneralPaperCodeSplitPrice.arithmetic_work model a code
    have hFound := GeneralPaperDecodeBucketPrice.arithmetic_work model a response
      (GeneralPaperCodeSplitExecution.run false model 1 code a.lambda).1.bucket
      (GeneralPaperCodeSplitExecution.run false model 1 code a.lambda).1.slot
    dsimp only
    change 67+(GeneralPaperCodeSplitExecution.run false model 1 code a.lambda).2+
      (GeneralPaperDecodeBucketExecution.run false model 1 a response
        (GeneralPaperCodeSplitExecution.run false model 1 code a.lambda).1.bucket
        (GeneralPaperCodeSplitExecution.run false model 1 code a.lambda).1.slot).2+4+64≤_
    omega
  · omega

theorem native_work (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) :
    (run bits model W a response code).1.work≤184*a.lambda+476 := by
  rw [data]
  exact GeneralPaperCodeDecodeWork.decode_work a response code

theorem same_data (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) :
    (run true model W a response code).1=(run false model 1 a response code).1 := by rw [data,data]

end Blotto.GeneralPaperCodeDecodePrice
