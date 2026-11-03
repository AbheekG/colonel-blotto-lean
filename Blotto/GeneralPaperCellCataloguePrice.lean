import Blotto.GeneralPaperCellCatalogueOperands

/-! Complete optional-entry catalogue fill, including one full lookup per
cell, endpoint reads, both native work additions and every array operation.
The outer index word and annotation cap come from retained/prefix sizes.
-/
namespace Blotto.GeneralPaperCellCataloguePrice
open GeneralPaperCodeAlphabet GeneralPaperCellCatalogueExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperCellCatalogueOperands (width)
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def queryProfile (model : RationalCostModel) (W n : ℕ) (a : Alphabet) : ℕ :=
  134217728*(a.lambda+3)*(GeneralPaperDecoderControls.controlWord W a.lambda+model.rat (width n a.lambda))+
    4*model.rat (width n a.lambda)+48*W

def profile (model : RationalCostModel) (W n : ℕ) (a : Alphabet) : ℕ :=
  n*queryProfile model W n a+44*(n+1)*arrayWord W n+128*W

def arithmeticProfile (n : ℕ) (a : Alphabet) : ℕ := n*(268435456*(a.lambda+3)+52)+44*(n+1)+128

theorem lookup_work (model : RationalCostModel) (W n : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hLo : lo≤8*a.C) (hHi : hi≤8*a.C) :
    (GeneralPaperLeastValidCellExecution.run true model W a response lo hi).2≤
      134217728*(a.lambda+3)*(GeneralPaperDecoderControls.controlWord W a.lambda+model.rat (width n a.lambda)) := by
  have h := GeneralPaperLeastValidCellPrice.bit_work model W a response lo hi hLo hHi
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone (by unfold width; omega)) _))

theorem fill_work {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n)
    (hBounds : ∀ r,(cells.read r).1≤8*a.C ∧ (cells.read r).2≤8*a.C) (count : ℕ) (hCount : count≤n) :
    (fill true (fun w => w) model W a response cells count hCount).2≤count*queryProfile model W n a+
      PaperIndexedArrayConstruction.overhead (fun w => w) (arrayWord W n) n count+64*W := by
  induction count with
  | zero => simp only [fill,PaperIndexedArrayConstruction.overhead,Nat.zero_mul,Nat.zero_add,slot,ite_true,le_refl]
  | succ count ih =>
    have hEarlier := ih (by omega)
    have hb := hBounds ⟨count,by omega⟩
    have hCall := lookup_work model W n a response (cells.read ⟨count,by omega⟩).1 (cells.read ⟨count,by omega⟩).2 hb.1 hb.2
    have hAdds := GeneralPaperCellCatalogueOperands.additions_work true (fun w => w) model W a response cells count hCount
    dsimp only at hAdds
    rw [fill,PaperIndexedArrayConstruction.overhead]
    dsimp only
    simp only [slot,ite_true,primitive]
    unfold queryProfile at hEarlier ⊢
    nlinarith only [hEarlier,hCall,hAdds]

theorem bit_work {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n)
    (hBounds : ∀ r,(cells.read r).1≤8*a.C ∧ (cells.read r).2≤8*a.C) :
    (run true (fun w => w) model W a response cells).2≤profile model W n a := by
  have hFill := fill_work model W a response cells hBounds n (Nat.le_refl _)
  have hOver := GeneralPaperControlArrayPrice.overhead (fun w => w) (arrayWord W n) n n
    (GeneralPaperSummaryArrayControls.array_word_positive W n) (Nat.le_refl _) (GeneralPaperSummaryArrayControls.array_index W n)
  unfold run profile
  dsimp only
  omega

theorem fill_arithmetic_work {n : ℕ} (model : RationalCostModel) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hCount : count≤n) :
    (fill false (fun _ => 1) model 1 a response cells count hCount).2≤
      count*(268435456*(a.lambda+3)+52)+PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 n count+64 := by
  induction count with
  | zero => simp only [fill,PaperIndexedArrayConstruction.overhead,Nat.zero_mul,Nat.zero_add,slot,Bool.false_eq_true,ite_false,Nat.mul_one,le_refl]
  | succ count ih =>
    have hEarlier := ih (by omega)
    have hCall := GeneralPaperLeastValidCellPrice.arithmetic_work model a response
      (cells.read ⟨count,by omega⟩).1 (cells.read ⟨count,by omega⟩).2
    rw [fill,PaperIndexedArrayConstruction.overhead]
    dsimp only
    simp only [slot,Bool.false_eq_true,ite_false,primitive,GeneralPaperNaturalPrimitivePrice.binary,Nat.mul_one]
    nlinarith only [hEarlier,hCall]

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (run false (fun _ => 1) model 1 a response cells).2≤arithmeticProfile n a := by
  have hFill := fill_arithmetic_work model a response cells n (Nat.le_refl _)
  have hOver := GeneralPaperControlArrayPrice.overhead (fun _ => 1) 1 n n (Nat.le_refl _) (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  unfold run arithmeticProfile
  dsimp only
  omega

theorem profile_mono (model : RationalCostModel) (W n N : ℕ) (a : Alphabet) (hN : n≤N) :
    profile model W n a≤profile model W N a := by
  have hw : width n a.lambda≤width N a.lambda := by
    have h := binaryWordWidth_mono (Nat.add_le_add_right hN 1)
    unfold width
    omega
  have hp := model.monotone hw
  have hCall := Nat.mul_le_mul_left (134217728*(a.lambda+3))
    (Nat.add_le_add_left hp (GeneralPaperDecoderControls.controlWord W a.lambda))
  have hQuery : queryProfile model W n a≤queryProfile model W N a := by
    unfold queryProfile
    omega
  have hFirst := Nat.mul_le_mul hN hQuery
  have hA : arrayWord W n≤arrayWord W N := by
    have h := binaryWordWidth_mono (Nat.add_le_add_right hN 1)
    unfold arrayWord
    omega
  have hSecond := Nat.mul_le_mul (Nat.mul_le_mul_left 44 (Nat.add_le_add_right hN 1)) hA
  exact Nat.add_le_add_right (Nat.add_le_add hFirst hSecond) _

theorem arithmetic_profile_mono (n N : ℕ) (a : Alphabet) (hN : n≤N) :
    arithmeticProfile n a≤arithmeticProfile N a := by
  have h := Nat.mul_le_mul_right (268435456*(a.lambda+3)+52) hN
  have hArray := Nat.mul_le_mul_left 44 (Nat.add_le_add_right hN 1)
  exact Nat.add_le_add_right (Nat.add_le_add h hArray) 128

end Blotto.GeneralPaperCellCataloguePrice
