import Blotto.GeneralPaperCodeScanExecution

/-! Guard values are bounded by actual code/cell endpoints. Native result
and suffix counters supply the scan's own annotation word caps. The fixed
five-candidate bound is analytical and adds no length or work-sum traversal.
-/
namespace Blotto.GeneralPaperCodeScanOperands
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeScanExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem guards_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (lo hi code : ℕ)
    (hLo : lo≤8*a.C) (hHi : hi≤8*a.C) (hCode : code≤8*a.C) :
    guards model.rat W lo hi code≤2*model.rat (operandWidth a.lambda)+64*W := by
  have hl := code_word a lo hLo
  have hh := code_word a hi hHi
  have hc := code_word a code hCode
  have hp := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone lo code _ hl hc
  have hq := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone code hi _ hc hh
  unfold guards
  omega

theorem evaluate_annotation (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b)
      (GeneralPaperCodeDecodeExecution.run true model W a response code).1.work 24≤2*model.rat (operandWidth a.lambda) := by
  have hw := GeneralPaperCodeDecodePrice.native_work true model W a response code
  exact metadata_binary model.rat model.monotone a.lambda _ _ 24
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)

theorem evaluate_native_work (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ) :
    (evaluate bits model W a response lo hi code).1.work≤184*a.lambda+500 := by
  rw [evaluate_data]
  exact GeneralPaperCodeMinimumScan.evaluate_work a response lo hi code

theorem scan_native_work (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (lo hi : ℕ) (codes : List ℕ) :
    (scan bits model W a response lo hi codes).1.work≤codes.length*(184*a.lambda+524)+8 := by
  rw [scan_data]
  exact GeneralPaperCodeMinimumScan.scan_work a response lo hi codes

theorem additions_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (lo hi code : ℕ) (rest : List ℕ) (hLength : (code::rest).length≤5) :
    additions model.rat (evaluate true model W a response lo hi code).1.work
      (scan true model W a response lo hi rest).1.work≤4*model.rat (operandWidth a.lambda) := by
  let tested := evaluate true model W a response lo hi code
  let later := scan true model W a response lo hi rest
  have ht := evaluate_native_work true model W a response lo hi code
  have hl := scan_native_work true model W a response lo hi rest
  have hLen : rest.length≤4 := by simp only [List.length_cons] at hLength; omega
  have hMul := Nat.mul_le_mul_right (184*a.lambda+524) hLen
  have hLater : later.1.work≤4*(184*a.lambda+524)+8 := hl.trans (by omega)
  change tested.1.work≤184*a.lambda+500 at ht
  have ha := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b) tested.1.work later.1.work
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  have hb := metadata_binary model.rat model.monotone a.lambda (fun a b => a+b) (tested.1.work+later.1.work) 24
    (by unfold metadataCap; omega) (by unfold metadataCap; omega) (by unfold metadataCap; omega)
  change additions model.rat tested.1.work later.1.work≤_
  unfold additions
  omega

end Blotto.GeneralPaperCodeScanOperands
