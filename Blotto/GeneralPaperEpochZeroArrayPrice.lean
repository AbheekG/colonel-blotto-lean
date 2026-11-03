import Blotto.GeneralPaperActualFieldDeltaPrice

/-! Local zero initialization uses one indexed fill, including literal-zero
writes, references and index/control costs. It agrees with the native level
initializer and does not materialize or copy a previous level array.
-/
namespace Blotto.GeneralPaperEpochZeroArrayPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run (bits : Bool) (index price : ℕ → ℕ) (W n : ℕ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W n else W) (fun _ => (0,price 1+16*W))

def profile (price : ℕ → ℕ) (W n : ℕ) : ℕ := n*(price 1+16*W)+44*(n+1)*arrayWord W n
def arithmeticProfile (n : ℕ) : ℕ := 17*n+44*(n+1)

theorem data (bits : Bool) (index price : ℕ → ℕ) (W n : ℕ) :
    (run bits index price W n).1=(GeneralPaperEpochLevelArray.initial n).1 := by
  simp only [run,GeneralPaperEpochLevelArray.initial,PaperIndexedArrayConstruction.run_data]

theorem bit_work (price : ℕ → ℕ) (W n : ℕ) : (run true (fun w => w) price W n).2≤profile price W n :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n) _ (fun _ => (0,price 1+16*W))
    (GeneralPaperSummaryArrayControls.array_word_positive W n) (GeneralPaperSummaryArrayControls.array_index W n) (fun _ => Nat.le_refl _)

theorem arithmetic_work (n : ℕ) : (run false (fun _ => 1) (fun _ => 1) 1 n).2≤arithmeticProfile n := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 17 (fun _ : Fin n => (0,17))
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun _ : Fin n => (0,17))).2≤17*n+44*(n+1)
  exact h.trans_eq (by ring)

theorem profile_mono (price : ℕ → ℕ) (W n N : ℕ) (hN : n≤N) : profile price W n≤profile price W N := by
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hN)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 44 (by omega : n+1≤N+1)) (GeneralPaperPlanProfileMonotonicity.array_word W n N hN))

theorem arithmetic_profile_mono (n N : ℕ) (hN : n≤N) : arithmeticProfile n≤arithmeticProfile N := by
  exact Nat.add_le_add (Nat.mul_le_mul_left 17 hN) (Nat.mul_le_mul_left 44 (by omega))

theorem every_prefix (bits : Bool) (index price : ℕ → ℕ) (W n count : ℕ) (hc : count≤n) :
    (PaperIndexedArrayConstruction.fill index (if bits then arrayWord W n else W)
      (fun _ : Fin n => (0,price 1+16*W)) count hc).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperEpochZeroArrayPrice
