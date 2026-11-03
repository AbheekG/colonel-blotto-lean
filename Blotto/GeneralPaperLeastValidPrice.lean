import Blotto.GeneralPaperLeastValidExecution

/-! Complete five-candidate least-valid lookup. Its actual starting guard
and split derive all candidate caps, and native result counters price the
final additions. No phase cost, valid-code oracle or extra scan is supplied.
-/
namespace Blotto.GeneralPaperLeastValidPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperLeastValidExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem additions_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    let split := GeneralPaperCodeSplitExecution.run true model W lo a.lambda
    let points := GeneralPaperLeastValidPointsPrice.run model.rat W split.1.bucket
    let found := GeneralPaperCodeScanExecution.scan true model W a response lo hi points.1
    additions model.rat split.1.work found.1.work≤4*model.rat (operandWidth a.lambda) := by
  let split := GeneralPaperCodeSplitExecution.run true model W lo a.lambda
  let points := GeneralPaperLeastValidPointsPrice.run model.rat W split.1.bucket
  let found := GeneralPaperCodeScanExecution.scan true model W a response lo hi points.1
  have hs : split.1.work≤14*a.lambda+42 := by
    dsimp only [split]
    rw [GeneralPaperCodeSplitExecution.data]
    exact GeneralPaperCodeSplit.run_work lo a.lambda
  have hf := GeneralPaperCodeScanOperands.scan_native_work true model W a response lo hi points.1
  rw [GeneralPaperLeastValidPointsPrice.length] at hf
  change found.1.work≤5*(184*a.lambda+524)+8 at hf
  have hp := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b) split.1.work found.1.work
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  have hq := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b) (split.1.work+found.1.work) 32
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  change additions model.rat split.1.work found.1.work≤_
  unfold additions
  omega

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hLo : lo≤8*a.C) (hHi : hi≤8*a.C) :
    (run true model W a response lo hi).2≤67108864*(a.lambda+3)*
      (controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  let P := model.rat (operandWidth a.lambda)
  let F := controlWord W a.lambda+P
  have hc := GeneralPaperCodeDecodePrice.control_work model W a lo hLo
  change _≤3*P+64*W at hc
  have hWF : W≤F := by dsimp [F,controlWord]; omega
  have hPF : P≤F := by dsimp only [F]; omega
  change _≤67108864*(a.lambda+3)*F
  unfold run
  dsimp only
  simp only [primitive,ite_true]
  split
  · rename_i hRange
    let split := GeneralPaperCodeSplitExecution.run true model W lo a.lambda
    let points := GeneralPaperLeastValidPointsPrice.run model.rat W split.1.bucket
    let found := GeneralPaperCodeScanExecution.scan true model W a response lo hi points.1
    have hb := GeneralPaperCodeSplitPrice.bucket_bound true model W a lo hRange
    have hs := GeneralPaperCodeSplitPrice.bit_work model W a lo hRange
    have hp := GeneralPaperLeastValidPointsPrice.bit_work model W a split.1.bucket hb
    have hf := GeneralPaperCodeScanPrice.bit_work model W a response lo hi hLo hHi points.1
      (by rw [GeneralPaperLeastValidPointsPrice.length])
      (GeneralPaperLeastValidPointsPrice.point_bound model.rat W a split.1.bucket hb)
    rw [GeneralPaperLeastValidPointsPrice.length] at hf
    have ha := additions_work model W a response lo hi
    change split.2≤4096*(a.lambda+3)*F at hs
    change points.2≤10*P+96*W at hp
    change found.2≤GeneralPaperCodeScanPrice.profile model W a 5 at hf
    unfold GeneralPaperCodeScanPrice.profile GeneralPaperCodeScanPrice.stepProfile GeneralPaperCodeEvaluatePrice.profile at hf
    change found.2≤5*(8388608*(a.lambda+3)*F+4*P+128*W+5*P+128*W)+64*W at hf
    change additions model.rat split.1.work found.1.work≤4*P at ha
    dsimp only
    change GeneralPaperCodeDecodeExecution.control model.rat W a lo+split.2+points.2+found.2+
      additions model.rat split.1.work found.1.work+64*W≤_
    nlinarith only [hc,hs,hp,hf,ha,hWF,hPF,Nat.zero_le (a.lambda*F)]
  · dsimp only
    nlinarith only [hc,hWF,hPF,Nat.zero_le (a.lambda*F)]

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run false model 1 a response lo hi).2≤134217728*(a.lambda+3) := by
  unfold run
  dsimp only
  simp only [primitive,Bool.false_eq_true,ite_false,GeneralPaperCodeDecodePrice.control_unit]
  split
  · let split := GeneralPaperCodeSplitExecution.run false model 1 lo a.lambda
    let points := GeneralPaperLeastValidPointsPrice.run (fun _ => 1) 1 split.1.bucket
    let found := GeneralPaperCodeScanExecution.scan false model 1 a response lo hi points.1
    have hs := GeneralPaperCodeSplitPrice.arithmetic_work model a lo
    have hp := GeneralPaperLeastValidPointsPrice.arithmetic_work split.1.bucket
    have hf := GeneralPaperCodeScanPrice.arithmetic_work model a response lo hi points.1
    rw [GeneralPaperLeastValidPointsPrice.length] at hf
    change split.2≤4096*(a.lambda+3) at hs
    change points.2=106 at hp
    change found.2≤GeneralPaperCodeScanPrice.arithmeticProfile a 5 at hf
    unfold GeneralPaperCodeScanPrice.arithmeticProfile GeneralPaperCodeEvaluatePrice.arithmeticProfile at hf
    dsimp only
    change 67+split.2+points.2+found.2+4+64≤_
    omega
  · omega

theorem native_work (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run bits model W a response lo hi).1.work≤934*a.lambda+2702 := by
  rw [data]
  exact GeneralPaperLeastValid.run_work a response lo hi

end Blotto.GeneralPaperLeastValidPrice
