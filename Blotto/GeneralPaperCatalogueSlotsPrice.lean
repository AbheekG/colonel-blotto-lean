import Blotto.GeneralPaperCatalogueSlotsExecution

/-! All padding branches, index arithmetic and one native closed-form
annotation construction. Words depend on the retained slot count, while
W remains the explicit global reference contribution.
-/
namespace Blotto.GeneralPaperCatalogueSlotsPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueSlotsExecution
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def magnitude (cap : ℕ) : ℕ := 128*(cap+2)
def width (cap : ℕ) : ℕ := 256+32*binaryWordWidth (cap+2)

theorem word_bound (cap : ℕ) : 1+binaryWordWidth (magnitude cap)≤width cap := by
  have h := binaryWordWidth_mul 128 (cap+2)
  have hc : binaryWordWidth 128=8 := by decide
  unfold magnitude width
  omega

theorem bounded_word (cap x : ℕ) (hx : x≤magnitude cap) : 1+binaryWordWidth x≤width cap :=
  (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans (word_bound cap)

theorem element_work {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (fallback : Entry)
    (raw : FixedArrayTable n (Option Entry)) (hCount : n≤cap) (i : Fin (cap+1)) :
    (element model.rat W fallback raw i).2≤4*model.rat (width cap)+192*W := by
  have hi := i.isLt
  have hM : cap+2≤magnitude cap := by unfold magnitude; omega
  have hn := bounded_word cap n (by omega)
  have hw := bounded_word cap i.val (by omega)
  have h0 := bounded_word cap 0 (by omega)
  have h1 := bounded_word cap 1 (by omega)
  have hj := bounded_word cap (i.val-1) (by omega)
  have hc := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone i.val 0 (width cap) hw h0
  have hs := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a-b) i.val 1 (width cap) hw h1 hj
  have hcj := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone (i.val-1) n (width cap) hj hn
  unfold element
  split
  · dsimp only; omega
  · dsimp only
    split <;> dsimp only <;> omega

theorem annotation_work (model : RationalCostModel) (cap : ℕ) :
    annotation model.rat cap≤6*model.rat (width cap) := by
  have hM : cap+2≤magnitude cap := by unfold magnitude; omega
  have hc := bounded_word cap cap (by omega)
  have h1 := bounded_word cap 1 (by omega)
  have hk := bounded_word cap (cap+1) (by omega)
  have h62 := bounded_word cap 62 (by unfold magnitude; omega)
  have h18 := bounded_word cap 18 (by unfold magnitude; omega)
  have hp := bounded_word cap (62*(cap+1)) (by unfold magnitude; omega)
  have hr := bounded_word cap (62*(cap+1)+18) (by unfold magnitude; omega)
  have ha := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) cap 1 (width cap) hc h1 hk
  have hb := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 62 (cap+1) (width cap) h62 hk hp
  have hd := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) (62*(cap+1)) 18 (width cap) hp h18 hr
  unfold annotation
  omega

def profile (model : RationalCostModel) (W cap : ℕ) : ℕ :=
  (cap+1)*(4*model.rat (width cap)+192*W)+44*(cap+2)*arrayWord W (cap+1)+6*model.rat (width cap)+128*W

def arithmeticProfile (cap : ℕ) : ℕ := (cap+1)*196+44*(cap+2)+134

theorem bit_work {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (raw : FixedArrayTable n (Option Entry)) (hCount : n≤cap) :
    (run (cap:=cap) true (fun w => w) model W a raw).2≤profile model W cap := by
  have hArray := GeneralPaperControlArrayPrice.indexed_work (n:=cap+1) (fun w => w) (arrayWord W (cap+1))
    (4*model.rat (width cap)+192*W)
    (element model.rat W (GeneralPaperCatalogueSlots.zero a) raw)
    (GeneralPaperSummaryArrayControls.array_word_positive W (cap+1))
    (GeneralPaperSummaryArrayControls.array_index W (cap+1))
    (element_work model W _ raw hCount)
  change _≤(cap+1)*(4*model.rat (width cap)+192*W)+44*(cap+2)*arrayWord W (cap+1) at hArray
  have hAnn := annotation_work model cap
  change (PaperIndexedArrayConstruction.run (fun w => w) (arrayWord W (cap+1))
    (element model.rat W (GeneralPaperCatalogueSlots.zero a) raw)).2+annotation model.rat cap+128*W≤_
  unfold profile
  omega

theorem element_arithmetic_work {n cap : ℕ} (fallback : Entry) (raw : FixedArrayTable n (Option Entry)) (i : Fin (cap+1)) :
    (element (fun _ => 1) 1 fallback raw i).2≤196 := by
  unfold element
  split
  · simp only [GeneralPaperIntegerWordPrice.compare,Nat.mul_one]; omega
  · dsimp only
    split <;> simp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary,Nat.mul_one] <;> omega

theorem arithmetic_work {n cap : ℕ} (model : RationalCostModel) (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) :
    (run (cap:=cap) false (fun _ => 1) model 1 a raw).2≤arithmeticProfile cap := by
  have hArray := GeneralPaperControlArrayPrice.indexed_work (n:=cap+1) (fun _ => 1) 1 196
    (element (cap:=cap) (fun _ => 1) 1 (GeneralPaperCatalogueSlots.zero a) raw) (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (element_arithmetic_work (cap:=cap) _ raw)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1
    (element (fun _ => 1) 1 (GeneralPaperCatalogueSlots.zero a) raw)).2+annotation (fun _ => 1) cap+128*1≤_
  simp only [annotation,GeneralPaperNaturalPrimitivePrice.binary] at *
  unfold arithmeticProfile
  omega

end Blotto.GeneralPaperCatalogueSlotsPrice
