import Blotto.GeneralPaperEpochPartitionPrice

/-! One reference fill retains each left endpoint. The native work counter
50*n+18 is formed once with multiplication/addition charged. Actual returned
partitions supply nonempty cells, containment and strict alphabet bounds.
-/
namespace Blotto.GeneralPaperCellRepresentativePrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def annotation (price : ℕ → ℕ) (n : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 50 n+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (50*n) 18

def run {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (FixedArrayTable n ℕ × ℕ) × ℕ :=
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W n else W)
    (fun r => ((cells.read r).1,16*W))
  ((filled.1,50*n+18),filled.2+annotation price n+64*W)

theorem data {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (run bits index price W cells).1=GeneralPaperCellRepresentatives.build cells := by
  apply Prod.ext
  · unfold run GeneralPaperCellRepresentatives.build
    dsimp only
    rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  · exact (GeneralPaperCellRepresentatives.work cells).symm

theorem read_data {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cells : GeneralPaperEpochCellInstructions.Cells n) (r : Fin n) :
    (run bits index price W cells).1.1.read r=(cells.read r).1 := by
  rw [data,GeneralPaperCellRepresentatives.read_build]

theorem annotation_work (price : ℕ → ℕ) (hMono : Monotone price) (n : ℕ) : annotation price n≤4*price (width n 0) := by
  have hW := GeneralPaperSignedCutOperands.word_bound n 0
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤magnitude n 0) (hb : b≤magnitude n 0) (hc : op a b≤magnitude n 0) :
      GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price (width n 0) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b (magnitude n 0) ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hW))
  have ha := p (fun a b => a*b) 50 n (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  have hb := p (fun a b => a+b) (50*n) 18 (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  unfold annotation
  omega

def profile (price : ℕ → ℕ) (W n : ℕ) : ℕ :=
  n*(16*W)+44*(n+1)*arrayWord W n+4*price (width n 0)+64*W

def arithmeticProfile (n : ℕ) : ℕ := n*16+44*(n+1)+68

theorem bit_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W : ℕ) (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (run true (fun w => w) price W cells).2≤profile price W n := by
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n) (16*W)
    (fun r : Fin n => ((cells.read r).1,16*W)) (GeneralPaperSummaryArrayControls.array_word_positive W n)
    (GeneralPaperSummaryArrayControls.array_index W n) (fun _ => Nat.le_refl _)
  exact Nat.add_le_add_right (Nat.add_le_add hA (annotation_work price hMono n)) _

theorem arithmetic_work {n : ℕ} (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (run false (fun _ => 1) (fun _ => 1) 1 cells).2≤arithmeticProfile n := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 16
    (fun r : Fin n => ((cells.read r).1,16)) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun r : Fin n => ((cells.read r).1,16))).2+4+64≤_
  unfold arithmeticProfile
  omega

theorem prepared_codes {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (r : Fin (GeneralPaperEpochPartitionPrice.run bits index price W U positions extras).1.count) :
    (run bits index price W (GeneralPaperEpochPartitionPrice.run bits index price W U positions extras).1.intervals).1.1.read r<U := by
  rw [read_data]
  have h := GeneralPaperEpochPartitionPrice.cell_bounds bits index price W U positions extras r
  exact h.1.trans_le h.2

theorem prepared_contains {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (r : Fin (GeneralPaperEpochPartitionPrice.run bits index price W U positions extras).1.count) :
    GeneralPaperEpochCellInstructions.Contains
      (GeneralPaperEpochPartitionPrice.run bits index price W U positions extras).1.intervals r
      ((run bits index price W (GeneralPaperEpochPartitionPrice.run bits index price W U positions extras).1.intervals).1.1.read r) := by
  rw [read_data]
  exact ⟨Nat.le_refl _,(GeneralPaperEpochPartitionPrice.cell_bounds bits index price W U positions extras r).1⟩

theorem every_prefix {n : ℕ} (index : ℕ → ℕ) (W A : ℕ) (cells : GeneralPaperEpochCellInstructions.Cells n)
    (count : ℕ) (hCount : count≤n) :
    (PaperIndexedArrayConstruction.fill index A (fun r => ((cells.read r).1,16*W)) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

theorem profile_mono (price : ℕ → ℕ) (hMono : Monotone price) (W n N : ℕ) (hN : n≤N) :
    profile price W n≤profile price W N := by
  have hw : width n 0≤width N 0 := by
    have h := binaryWordWidth_mono (Nat.add_le_add_right hN 2)
    unfold width
    omega
  have hA : arrayWord W n≤arrayWord W N := by
    have h := binaryWordWidth_mono (Nat.add_le_add_right hN 1)
    unfold arrayWord
    omega
  have hFirst := Nat.mul_le_mul_right (16*W) hN
  have hSecond := Nat.mul_le_mul (Nat.mul_le_mul_left 44 (Nat.add_le_add_right hN 1)) hA
  have hThird := Nat.mul_le_mul_left 4 (hMono hw)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hFirst hSecond) hThird) _

theorem arithmetic_profile_mono (n N : ℕ) (hN : n≤N) : arithmeticProfile n≤arithmeticProfile N := by
  have hFirst := Nat.mul_le_mul_right 16 hN
  have hSecond := Nat.mul_le_mul_left 44 (Nat.add_le_add_right hN 1)
  exact Nat.add_le_add_right (Nat.add_le_add hFirst hSecond) _

end Blotto.GeneralPaperCellRepresentativePrice
