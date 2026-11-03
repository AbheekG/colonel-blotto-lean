import Blotto.GeneralPaperCodeDecodePrice

/-! The least-valid lookup constructs exactly five candidates from one
retained starting bucket. One shared base multiplication and four additions
are priced. Actual split/guard data derives every decoder-input code cap.
-/
namespace Blotto.GeneralPaperLeastValidPointsPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (primitive : ℕ → ℕ) (W bucket : ℕ) : List ℕ × ℕ :=
  let base := 4*bucket
  ([base,base+1,base+2,base+3,base+4],
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 4 bucket+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) base 1+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) base 2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) base 3+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) base 4+96*W)

theorem data (primitive : ℕ → ℕ) (W bucket : ℕ) : (run primitive W bucket).1=GeneralPaperLeastValid.points bucket := rfl

theorem length (primitive : ℕ → ℕ) (W bucket : ℕ) : (run primitive W bucket).1.length=5 := rfl

theorem point_bound (primitive : ℕ → ℕ) (W : ℕ) (a : Alphabet) (bucket : ℕ) (hBucket : bucket≤a.C)
    (code : ℕ) (hCode : code∈(run primitive W bucket).1) : code≤8*a.C := by
  have hc := a.scalePositive
  rw [data] at hCode
  simp only [GeneralPaperLeastValid.points,List.mem_cons,List.not_mem_nil,or_false] at hCode
  rcases hCode with h|h|h|h|h <;> omega

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (bucket : ℕ) (hBucket : bucket≤a.C) :
    (run model.rat W bucket).2≤10*model.rat (operandWidth a.lambda)+96*W := by
  have hc := a.scalePositive
  have hWord := code_word a (8*a.C) (Nat.le_refl _)
  have price (op : ℕ → ℕ → ℕ) (x y : ℕ) (hx : x≤8*a.C) (hy : y≤8*a.C) (hz : op x y≤8*a.C) :
      GeneralPaperNaturalPrimitivePrice.binary model.rat op x y≤2*model.rat (operandWidth a.lambda) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone op x y (8*a.C) hx hy hz).trans
      (Nat.mul_le_mul_left 2 (model.monotone hWord))
  have hBase := price (fun a b => a*b) 4 bucket (by omega) (by omega) (by omega)
  have add (j : ℕ) (hj : j≤4) :
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (4*bucket) j≤2*model.rat (operandWidth a.lambda) :=
    price (fun a b => a+b) (4*bucket) j (by omega) (by omega) (by omega)
  have h1 := add 1 (by omega)
  have h2 := add 2 (by omega)
  have h3 := add 3 (by omega)
  have h4 := add 4 (Nat.le_refl _)
  unfold run
  dsimp only
  omega

theorem arithmetic_work (bucket : ℕ) : (run (fun _ => 1) 1 bucket).2=106 := rfl

theorem guarded_decoder_call (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (lo : ℕ) (hLo : lo≤4*a.C) (code : ℕ)
    (hCode : code∈(run model.rat W (GeneralPaperCodeSplitExecution.run true model W lo a.lambda).1.bucket).1) :
    (GeneralPaperCodeDecodeExecution.run true model W a response code).2≤8388608*(a.lambda+3)*
      (controlWord W a.lambda+model.rat (operandWidth a.lambda)) :=
  GeneralPaperCodeDecodePrice.bit_work model W a response code
    (point_bound model.rat W a _ (GeneralPaperCodeSplitPrice.bucket_bound true model W a lo hLo) code hCode)

theorem division_control (W lambda fuel : ℕ) (hFuel : fuel≤lambda+2) :
    GeneralPaperQuotientRegisterSpace.counterWord fuel≤controlWord W lambda := by
  have h := binaryWordWidth_mono (Nat.add_le_add_right hFuel 1)
  have hc := quotient_control W lambda
  unfold GeneralPaperQuotientRegisterSpace.counterWord at hc ⊢
  omega

end Blotto.GeneralPaperLeastValidPointsPrice
