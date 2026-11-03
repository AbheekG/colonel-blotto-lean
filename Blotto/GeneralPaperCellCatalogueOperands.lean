import Blotto.GeneralPaperCellCatalogueData

/-! Prefix-derived lookup-work magnitudes for the catalogue fill. The code
word includes lambda, while array indices and accumulated annotations also
include the retained cell count. No external counter cap or sum pass is used.
-/
namespace Blotto.GeneralPaperCellCatalogueOperands
open GeneralPaperCodeAlphabet GeneralPaperCellCatalogueExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def entryBound (lambda : ℕ) : ℕ := 934*lambda+2772
def magnitude (n lambda : ℕ) : ℕ := 8192*(n+1)*(lambda+1)+8192
def width (n lambda : ℕ) : ℕ := GeneralPaperDecoderControls.operandWidth lambda+256+32*binaryWordWidth (n+1)

theorem fill_annotation {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hCount : count≤n) :
    (fill bits index model W a response cells count hCount).1.2≤count*entryBound a.lambda+18 := by
  induction count with
  | zero => simp only [fill,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
    have hEarlier := ih (by omega)
    have hCell := GeneralPaperLeastValidCellPrice.native_work bits model W a response
      (cells.read ⟨count,by omega⟩).1 (cells.read ⟨count,by omega⟩).2
    rw [fill]
    dsimp only
    unfold entryBound at *
    nlinarith only [hEarlier,hCell]

theorem annotation_cap (n lambda count : ℕ) (hCount : count≤n) :
    count*entryBound lambda+18≤magnitude n lambda := by
  have hEntry : entryBound lambda≤8192*(lambda+1) := by unfold entryBound; omega
  have h := Nat.mul_le_mul hCount hEntry
  unfold magnitude
  nlinarith only [h,Nat.zero_le lambda]

theorem word_bound (n lambda : ℕ) : 1+binaryWordWidth (magnitude n lambda)≤width n lambda := by
  have ha := binaryWordWidth_mul 8192 (n+1)
  have hb := binaryWordWidth_mul (8192*(n+1)) (lambda+1)
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (8192*(n+1)*(lambda+1)) 8192
  have h8192 : binaryWordWidth 8192=14 := by decide
  have hl := GeneralPaperInitializerControlCounters.word_le_self (lambda+1)
  unfold magnitude width GeneralPaperDecoderControls.operandWidth
  omega

theorem additions_work {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hCount : count+1≤n) :
    let earlier := fill bits index model W a response cells count (by omega)
    let found := GeneralPaperLeastValidCellExecution.run bits model W a response
      (cells.read ⟨count,by omega⟩).1 (cells.read ⟨count,by omega⟩).2
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) earlier.1.2 found.1.work+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (earlier.1.2+found.1.work) 54≤
        4*model.rat (width n a.lambda) := by
  let earlier := fill bits index model W a response cells count (by omega)
  let found := GeneralPaperLeastValidCellExecution.run bits model W a response
    (cells.read ⟨count,by omega⟩).1 (cells.read ⟨count,by omega⟩).2
  have hFull := (fill_annotation bits index model W a response cells (count+1) hCount).trans
    (annotation_cap n a.lambda (count+1) hCount)
  rw [fill] at hFull
  change earlier.1.2+found.1.work+54≤magnitude n a.lambda at hFull
  have hWord := word_bound n a.lambda
  have price (x y : ℕ) (hx : x≤magnitude n a.lambda) (hy : y≤magnitude n a.lambda) (hz : x+y≤magnitude n a.lambda) :
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) x y≤2*model.rat (width n a.lambda) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone _ x y (magnitude n a.lambda) hx hy hz).trans
      (Nat.mul_le_mul_left 2 (model.monotone hWord))
  have ha := price earlier.1.2 found.1.work (by omega) (by omega) (by omega)
  have hb := price (earlier.1.2+found.1.work) 54 (by omega) (by omega) hFull
  change GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) earlier.1.2 found.1.work+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (earlier.1.2+found.1.work) 54≤_
  omega

end Blotto.GeneralPaperCellCatalogueOperands
