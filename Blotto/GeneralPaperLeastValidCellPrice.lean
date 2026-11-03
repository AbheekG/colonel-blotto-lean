import Blotto.GeneralPaperLeastValidCellExecution

/-! Full half-open cell prices, including the empty branch, strict guard,
upper-endpoint subtraction and native return annotation addition.
-/
namespace Blotto.GeneralPaperLeastValidCellPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperLeastValidCellExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem subtraction_work (model : RationalCostModel) (a : Alphabet) (hi : ℕ) (hHi : hi≤8*a.C) :
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) hi 1≤2*model.rat (operandWidth a.lambda) := by
  have hWord := code_word a (8*a.C) (Nat.le_refl _)
  exact (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone _ hi 1 (8*a.C)
    hHi (by have hc:=a.scalePositive; omega) (by omega)).trans (Nat.mul_le_mul_left 2 (model.monotone hWord))

theorem annotation_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b)
      (GeneralPaperLeastValidExecution.run true model W a response lo (hi-1)).1.work 16≤2*model.rat (operandWidth a.lambda) := by
  have h := GeneralPaperLeastValidPrice.native_work true model W a response lo (hi-1)
  exact metadata_binary model.rat model.monotone a.lambda _ _ 16
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hLo : lo≤8*a.C) (hHi : hi≤8*a.C) :
    (run true model W a response lo hi).2≤134217728*(a.lambda+3)*
      (controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  let P := model.rat (operandWidth a.lambda)
  let F := controlWord W a.lambda+P
  have hGuard := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone lo hi (operandWidth a.lambda)
    (code_word a lo hLo) (code_word a hi hHi)
  have hSub := subtraction_work model a hi hHi
  have hAnn := annotation_work model W a response lo hi
  have hCall := GeneralPaperLeastValidPrice.bit_work model W a response lo (hi-1) hLo (by omega)
  change _≤P at hGuard
  change _≤2*P at hSub hAnn
  change _≤67108864*(a.lambda+3)*F at hCall
  have hWF : W≤F := by dsimp [F,controlWord]; omega
  have hPF : P≤F := by dsimp only [F]; omega
  change _≤134217728*(a.lambda+3)*F
  unfold run
  dsimp only
  simp only [primitive,ite_true]
  split <;> dsimp only <;> nlinarith only [hGuard,hSub,hAnn,hCall,hWF,hPF,Nat.zero_le (a.lambda*F)]

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run false model 1 a response lo hi).2≤268435456*(a.lambda+3) := by
  have hCall := GeneralPaperLeastValidPrice.arithmetic_work model a response lo (hi-1)
  unfold run
  dsimp only
  simp only [primitive,Bool.false_eq_true,ite_false,GeneralPaperIntegerWordPrice.compare]
  split
  · dsimp only
    change 65+(GeneralPaperLeastValidExecution.run false model 1 a response lo (hi-1)).2+2+2+64≤_
    omega
  · omega

theorem native_work (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run bits model W a response lo hi).1.work≤934*a.lambda+2718 := by
  rw [data]
  exact GeneralPaperLeastValidCell.run_work a response lo hi

theorem same_data (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run true model W a response lo hi).1=(run false model 1 a response lo hi).1 := by rw [data,data]

end Blotto.GeneralPaperLeastValidCellPrice
