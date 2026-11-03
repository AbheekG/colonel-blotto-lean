import Blotto.GeneralPaperCachedCatalogueExecution

/-! Complete per-summary partition/lookup/padding prices. Actual clipped
boundaries and the returned partition count derive all local premises.
-/
namespace Blotto.GeneralPaperCachedCataloguePrice
open GeneralPaperCodeAlphabet GeneralPaperCachedCatalogueExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def finishProfile (model : RationalCostModel) (W n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCellCataloguePrice.profile model W (n+1) a+GeneralPaperCatalogueSlotsPrice.profile model W (n+1)+128*W

def finishArithmeticProfile (n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCellCataloguePrice.arithmeticProfile (n+1) a+GeneralPaperCatalogueSlotsPrice.arithmeticProfile (n+1)+128

def profile (model : RationalCostModel) (W n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCataloguePartitionPrice.profile model.rat W n (8*a.C)+finishProfile model W n a+
    (2*model.rat (GeneralPaperDecoderControls.operandWidth a.lambda)+2*model.rat (GeneralPaperCatalogueSlotsPrice.width (n+1)))+128*W

def arithmeticProfile (n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCataloguePartitionPrice.arithmeticProfile n+finishArithmeticProfile n a+4+128

theorem finish_work (n : ℕ) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (part : GeneralPaperPreparedPartition.Prepared) (hCount : part.count≤n+1)
    (hBounds : ∀ r,(part.intervals.read r).1≤8*a.C ∧ (part.intervals.read r).2≤8*a.C) :
    (finish n true (fun w => w) model W a response part).2≤finishProfile model W n a := by
  have hRaw := (GeneralPaperCellCataloguePrice.bit_work model W a response part.intervals hBounds).trans
    (GeneralPaperCellCataloguePrice.profile_mono model W part.count (n+1) a hCount)
  have hPad := GeneralPaperCatalogueSlotsPrice.bit_work (cap:=n+1) model W a
    (GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response part.intervals).1.1 hCount
  exact Nat.add_le_add_right (Nat.add_le_add hRaw hPad) _

theorem finish_arithmetic_work (n : ℕ) (model : RationalCostModel) (a : Alphabet) (response : Bool)
    (part : GeneralPaperPreparedPartition.Prepared) (hCount : part.count≤n+1) :
    (finish n false (fun _ => 1) model 1 a response part).2≤finishArithmeticProfile n a := by
  have hRaw := (GeneralPaperCellCataloguePrice.arithmetic_work model a response part.intervals).trans
    (GeneralPaperCellCataloguePrice.arithmetic_profile_mono part.count (n+1) a hCount)
  have hPad := GeneralPaperCatalogueSlotsPrice.arithmetic_work (cap:=n+1) model a
    (GeneralPaperCellCatalogueExecution.run false (fun _ => 1) model 1 a response part.intervals).1.1
  exact Nat.add_le_add_right (Nat.add_le_add hRaw hPad) _

theorem header_work (model : RationalCostModel) (n : ℕ) (a : Alphabet) :
    header model.rat n a≤2*model.rat (GeneralPaperDecoderControls.operandWidth a.lambda)+
      2*model.rat (GeneralPaperCatalogueSlotsPrice.width (n+1)) := by
  have hc := a.scalePositive
  have h8 := GeneralPaperDecoderControls.code_word a 8 (by omega)
  have hC := GeneralPaperDecoderControls.code_word a a.C (by omega)
  have hU := GeneralPaperDecoderControls.code_word a (8*a.C) (Nat.le_refl _)
  have hMul := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 8 a.C _ h8 hC hU
  have hw (x : ℕ) (hx : x≤n+1) : 1+binaryWordWidth x≤GeneralPaperCatalogueSlotsPrice.width (n+1) :=
    GeneralPaperCatalogueSlotsPrice.bounded_word (n+1) x (by unfold GeneralPaperCatalogueSlotsPrice.magnitude; omega)
  have hAdd := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) n 1 _
    (hw n (by omega)) (hw 1 (by omega)) (hw (n+1) (Nat.le_refl _))
  exact Nat.add_le_add hMul hAdd

theorem bit_work {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summary : FixedArrayTable n ℕ) (hCodes : ∀ r,summary.read r<2*(8*a.C)) :
    (run true (fun w => w) model W a response summary).2≤profile model W n a := by
  have hPart := GeneralPaperCataloguePartitionPrice.bit_work model.rat model.monotone W (8*a.C) summary hCodes
  have hFinish := finish_work n model W a response
    (GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary).1
    (GeneralPaperCataloguePartitionPrice.count_bound true (fun w => w) model.rat W (8*a.C) summary)
    (GeneralPaperActualCellCatalogue.endpoints_bound true (fun w => w) model.rat W (8*a.C) summary)
  have hHeader := header_work model n a
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hPart hFinish) hHeader) _

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (a : Alphabet) (response : Bool)
    (summary : FixedArrayTable n ℕ) (hCodes : ∀ r,summary.read r<2*(8*a.C)) :
    (run false (fun _ => 1) model 1 a response summary).2≤arithmeticProfile n a := by
  have hPart := GeneralPaperCataloguePartitionPrice.arithmetic_work (8*a.C) summary hCodes
  have hFinish := finish_arithmetic_work n model a response
    (GeneralPaperCataloguePartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) summary).1
    (GeneralPaperCataloguePartitionPrice.count_bound false (fun _ => 1) (fun _ => 1) 1 (8*a.C) summary)
  have hHeader : header (fun _ => 1) n a=4 := rfl
  change _≤GeneralPaperCataloguePartitionPrice.arithmeticProfile n+finishArithmeticProfile n a+4+128
  change (GeneralPaperCataloguePartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) summary).2+
    (finish n false (fun _ => 1) model 1 a response
      (GeneralPaperCataloguePartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) summary).1).2+
      header (fun _ => 1) n a+128≤_
  rw [hHeader]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hPart hFinish) 4) 128

end Blotto.GeneralPaperCachedCataloguePrice
