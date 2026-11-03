import Blotto.GeneralPaperSignedTailCalibration

/-! Adjacent boundary pairs are materialized once. The successor index,
two retained boundary reads, pair write and complete array loop are priced.
The local index word comes from the retained boundary count.
-/
namespace Blotto.GeneralPaperBoundaryCellPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def width (n : ℕ) : ℕ := 64+8*binaryWordWidth (n+2)

def element {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (boundary : FixedArrayTable (n+1) ℕ) (r : Fin n) :
    (ℕ × ℕ) × ℕ :=
  let next := r.val+1
  ((boundary.read r.castSucc,boundary.read ⟨next,by have := r.isLt; omega⟩),
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) r.val 1+48*W)

def run {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W : ℕ) (boundary : FixedArrayTable (n+1) ℕ) :
    GeneralPaperEpochCellInstructions.Cells n × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W n else W) (element primitive W boundary)

def profile (primitive : ℕ → ℕ) (W n : ℕ) : ℕ :=
  n*(2*primitive (width n)+48*W)+44*(n+1)*arrayWord W n

def arithmeticProfile (n : ℕ) : ℕ := n*50+44*(n+1)

theorem element_data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (boundary : FixedArrayTable (n+1) ℕ) (r : Fin n) :
    (element primitive W boundary r).1=(boundary.read r.castSucc,boundary.read r.succ) := rfl

theorem data {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W : ℕ) (boundary : FixedArrayTable (n+1) ℕ) :
    (run bits index primitive W boundary).1=GeneralPaperBoundaryCells.cells boundary := by
  rw [run,PaperIndexedArrayConstruction.run_data]
  rfl

theorem increment_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (n i : ℕ) (hi : i≤n) :
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) i 1≤2*primitive (width n) := by
  have hWord : 1+binaryWordWidth (n+1)≤width n := by
    have h := binaryWordWidth_mono (show n+1≤n+2 by omega)
    unfold width
    omega
  exact (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono _ i 1 (n+1)
    (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hWord))

theorem bit_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ) (boundary : FixedArrayTable (n+1) ℕ) :
    (run true (fun w => w) primitive W boundary).2≤profile primitive W n := by
  apply GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n) (2*primitive (width n)+48*W)
    (element primitive W boundary) (GeneralPaperSummaryArrayControls.array_word_positive W n)
    (GeneralPaperSummaryArrayControls.array_index W n)
  intro r
  exact Nat.add_le_add_right (increment_work primitive hMono n r.val (Nat.le_of_lt r.isLt)) _

theorem arithmetic_work {n : ℕ} (boundary : FixedArrayTable (n+1) ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 boundary).2≤arithmeticProfile n := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 50 (element (fun _ => 1) 1 boundary)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  simpa only [run,Bool.false_eq_true,ite_false,arithmeticProfile,Nat.mul_one] using h

theorem profile_mono (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W n N : ℕ) (hN : n≤N) :
    profile primitive W n≤profile primitive W N := by
  have hw : width n≤width N := by
    have h := binaryWordWidth_mono (show n+2≤N+2 by omega)
    unfold width
    omega
  have hA : arrayWord W n≤arrayWord W N := by
    have h := binaryWordWidth_mono (Nat.add_le_add_right hN 1)
    unfold arrayWord
    omega
  have hFirst := Nat.mul_le_mul hN (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hMono hw)) (48*W))
  have hSecond := Nat.mul_le_mul (Nat.mul_le_mul_left 44 (Nat.add_le_add_right hN 1)) hA
  exact Nat.add_le_add hFirst hSecond

theorem arithmetic_profile_mono (n N : ℕ) (hN : n≤N) : arithmeticProfile n≤arithmeticProfile N := by
  unfold arithmeticProfile
  omega

end Blotto.GeneralPaperBoundaryCellPrice
