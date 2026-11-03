import Blotto.GeneralPaperDecodeBucketExecution

/-! Complete grid/open/interior bucket prices. Actual split bounds supply
the code-word caps. Midpoint return annotations are bounded from native
query execution, and their addition is charged before the result write.
-/
namespace Blotto.GeneralPaperDecodeBucketPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperDecodeBucketExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem control_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (bucket slot : ℕ)
    (hBucket : bucket≤a.C) (hSlot : slot<4) :
    GeneralPaperDecodeBucketExecution.control model.rat W a bucket slot≤6*model.rat (operandWidth a.lambda)+128*W := by
  let L := operandWidth a.lambda
  have hb := code_word a bucket (by have hc:=a.scalePositive; omega)
  have hc := code_word a a.C (by have hc:=a.scalePositive; omega)
  have hs := code_word a slot (by have hc:=a.scalePositive; omega)
  have hbc := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone bucket a.C L hb hc
  have test (j : ℕ) (hj : j≤3) : GeneralPaperIntegerWordPrice.compare model.rat slot j≤model.rat L :=
    GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone slot j L hs
      (code_word a j (by have hc:=a.scalePositive; omega))
  have h0 := test 0 (by omega)
  have h1 := test 1 (by omega)
  have h2 := test 2 (by omega)
  have h3 := test 3 (by omega)
  unfold GeneralPaperDecodeBucketExecution.control
  change _≤6*model.rat L+128*W
  omega

theorem annotation_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (bucket : ℕ) (hBucket : bucket<a.C) :
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b)
      (GeneralPaperDecoderMidpointPrice.run true model W false a bucket).1.work 48≤2*model.rat (operandWidth a.lambda) := by
  have h := GeneralPaperDecoderMidpointPrice.native_work true model W false a bucket hBucket
  exact metadata_binary model.rat model.monotone a.lambda _ _ 48
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ)
    (hBucket : bucket≤a.C) (hSlot : slot<4) :
    (run true model W a response bucket slot).2≤4194304*(a.lambda+3)*
      (controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  let P := model.rat (operandWidth a.lambda)
  let F := controlWord W a.lambda+P
  have hControl := control_work model W a bucket slot hBucket hSlot
  change _≤6*P+128*W at hControl
  have hWF : W≤F := by dsimp [F,controlWord]; omega
  have hPF : P≤F := by dsimp only [F]; omega
  have simple : GeneralPaperDecodeBucketExecution.control model.rat W a bucket slot+64*W≤4194304*(a.lambda+3)*F := by
    nlinarith only [hControl,hWF,hPF,Nat.zero_le (a.lambda*F)]
  change _≤4194304*(a.lambda+3)*F
  rw [GeneralPaperDecodeBucketExecution.run,ite_eq_left hBucket]
  dsimp only
  simp only [primitive,ite_true]
  split
  · exact simple
  · split
    · split <;> exact simple
    · split
      · rename_i hMode
        have hMid := GeneralPaperDecoderMidpointPrice.bit_work model W false a bucket hMode.1
        have hAnn := annotation_work model W a bucket hMode.1
        change _≤2097152*(a.lambda+3)*F at hMid
        change _≤2*P at hAnn
        dsimp only
        nlinarith only [hControl,hMid,hAnn,hWF,hPF,Nat.zero_le (a.lambda*F)]
      · exact simple

theorem control_unit (a : Alphabet) (bucket slot : ℕ) :
    GeneralPaperDecodeBucketExecution.control (fun _ => 1) 1 a bucket slot=134 := rfl

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (response : Bool) (bucket slot : ℕ) :
    (run false model 1 a response bucket slot).2≤8388608*(a.lambda+3) := by
  unfold run
  dsimp only
  simp only [primitive,Bool.false_eq_true,ite_false,control_unit]
  split
  · split
    · omega
    · split
      · split <;> omega
      · split
        · rename_i hMode
          have hMid := GeneralPaperDecoderMidpointPrice.arithmetic_work model false a bucket hMode.1
          dsimp only
          change 134+(GeneralPaperDecoderMidpointPrice.run false model 1 false a bucket).2+2+64≤_
          omega
        · omega
  · omega

theorem native_work (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ) :
    (run bits model W a response bucket slot).1.work≤170*a.lambda+418 := by
  rw [data]
  exact GeneralPaperCodeDecodeWork.bucket_work a response bucket slot

end Blotto.GeneralPaperDecodeBucketPrice
