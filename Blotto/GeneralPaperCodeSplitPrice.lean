import Blotto.GeneralPaperCodeSplitExecution

/-! Full code-split costs with native bucket/slot/work correspondence.
The bit path uses streaming constructed division at a derived control word;
the unit path uses the arithmetic-only constructed-division program.
-/
namespace Blotto.GeneralPaperCodeSplitPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeSplitExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem division_width (a : Alphabet) (code : ℕ) (hCode : code≤4*a.C) :
    GeneralPaperQuotientRegisterSpace.operandWord code 4≤operandWidth a.lambda := by
  have hSmall : code<2^a.lambda := by rw [←a.dyadic]; have hc:=a.scalePositive; omega
  have hc := GeneralPaperCFOperandPrice.small_word a.lambda code hSmall
  have h4 : binaryWordWidth 4=3 := by decide
  have h := GeneralPaperGrowingQuotientBits.magnitude_width code 4
  change GeneralPaperQuotientRegisterSpace.operandWord code 4≤GeneralPaperGrowingQuotientBits.width code 4 at h
  apply h.trans
  unfold GeneralPaperGrowingQuotientBits.width operandWidth
  omega

theorem annotation_work (model : RationalCostModel) (a : Alphabet) (code : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) a.lambda 1+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b)
        (GeneralPaperConstructedNatDivision.run code 4 (a.lambda+1)).work 12≤4*model.rat (operandWidth a.lambda) := by
  have hd := GeneralPaperConstructedNatDivision.depth_le_fuel code 4 (a.lambda+1)
  have hw := GeneralPaperConstructedNatDivision.work_depth code 4 (a.lambda+1)
  have hCap : (GeneralPaperConstructedNatDivision.run code 4 (a.lambda+1)).work+12≤14*a.lambda+42 := by omega
  have hf := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b) a.lambda 1
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  have hr := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b)
    (GeneralPaperConstructedNatDivision.run code 4 (a.lambda+1)).work 12
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  omega

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hCode : code≤4*a.C) :
    (run true model W code a.lambda).2≤4096*(a.lambda+3)*
      (controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  let A := controlWord W a.lambda
  let P := model.rat (operandWidth a.lambda)
  let F := A+P
  have hd := GeneralPaperConstructedNatDivision.depth_le_fuel code 4 (a.lambda+1)
  have hDiv := GeneralPaperStreamingNatDivision.priced_work model A code 4 (a.lambda+1) (by decide)
  have hLift := Nat.mul_le_mul
    (Nat.mul_le_mul_left 1024 (show (GeneralPaperConstructedNatDivision.run code 4 (a.lambda+1)).depth+1≤a.lambda+2 by omega))
    (Nat.add_le_add_left (model.monotone (division_width a code hCode)) A)
  have hBound := hDiv.trans hLift
  have hMeta := annotation_work model a code
  have hWF : W≤F := by dsimp [F,A,controlWord]; omega
  have hPF : P≤F := by dsimp only [F]; omega
  unfold run
  simp only [ite_true,GeneralPaperStreamingNatDivision.priced_data]
  change (GeneralPaperStreamingNatDivision.priced model A code 4 (a.lambda+1)).2+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) a.lambda 1+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b)
      (GeneralPaperConstructedNatDivision.run code 4 (a.lambda+1)).work 12+96*W≤4096*(a.lambda+3)*F
  change _≤1024*(a.lambda+2)*F at hBound
  change _≤4*P at hMeta
  nlinarith only [hBound,hMeta,hWF,hPF,Nat.zero_le (a.lambda*F)]

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (code : ℕ) :
    (run false model 1 code a.lambda).2≤4096*(a.lambda+3) := by
  have h := GeneralPaperConstructedNatDivisionBits.unit_work code 4 (a.lambda+1) (by decide)
  have hd := GeneralPaperConstructedNatDivision.depth_le_fuel code 4 (a.lambda+1)
  change (GeneralPaperConstructedNatDivisionBits.run (fun _ => 1) 1 code 4 (a.lambda+1)).2+100≤_
  omega

theorem specification (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hCode : code≤4*a.C) :
    code=4*(run bits model W code a.lambda).1.bucket+(run bits model W code a.lambda).1.slot ∧
      (run bits model W code a.lambda).1.slot<4 := by
  rw [data]
  exact GeneralPaperCodeSplit.run_spec a code hCode

theorem bucket_bound (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hCode : code≤4*a.C) :
    (run bits model W code a.lambda).1.bucket≤a.C := by
  have h := specification bits model W a code hCode
  omega

end Blotto.GeneralPaperCodeSplitPrice
