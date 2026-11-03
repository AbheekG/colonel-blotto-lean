import Blotto.GeneralPaperIndexedArrayLifetime

/-! The actual length-coordinate activation: all loaded/written rationals,
the conversion and two primitive scratch charges, and scalar work fields.
Every indexed-array cursor retains its actual partial output and frames. -/
namespace Blotto.GeneralPaperEqualLengthLifetime
open GeneralPaperEncodedScalarStorage (natBits fields fields_bound)
open GeneralPaperIndexedArrayLifetime (prefixTable window frame)
open GeneralPaperEncodedBasisStorage (arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def coordinateFrame (model : RationalCostModel) (A : ℕ) (D : ℚ) (a : ℕ) : ℕ :=
  let num := GeneralPaperRationalScalarStep.natural A a
  let quotient := GeneralPaperRationalScalarStep.run model A .div num.1 D
  let doubled := GeneralPaperRationalScalarStep.run model A .mul 2 quotient.1
  natBits a + rationalWordWidth D + rationalWordWidth (2 : ℚ) +
    rationalWordWidth num.1 + rationalWordWidth quotient.1 + rationalWordWidth doubled.1 +
    (num.2 + quotient.2 + doubled.2) +
    fields A [num.2, quotient.2, doubled.2, num.2 + quotient.2,
      num.2 + quotient.2 + doubled.2, (GeneralPaperEqualLengthArray.coordinate model A D a).2,
      A, 16 * A, 16] + 128 * A

theorem coordinate_frame_le (model : RationalCostModel) (A : ℕ) (D : ℚ) (a : ℕ) :
    coordinateFrame model A D a ≤ 128 * ((GeneralPaperEqualLengthArray.coordinate model A D a).2 + A + 1) := by
  let num := GeneralPaperRationalScalarStep.natural A a
  let quotient := GeneralPaperRationalScalarStep.run model A .div num.1 D
  let doubled := GeneralPaperRationalScalarStep.run model A .mul 2 quotient.1
  let C := (GeneralPaperEqualLengthArray.coordinate model A D a).2
  have hC : C = num.2 + quotient.2 + doubled.2 + 16 * A + 16 := rfl
  have hNat : natBits a + rationalWordWidth num.1 ≤ num.2 + 1 := by
    unfold num GeneralPaperRationalScalarStep.natural natBits
    dsimp only
    omega
  have hQuot : rationalWordWidth D + rationalWordWidth quotient.1 ≤ quotient.2 := by
    unfold quotient GeneralPaperRationalScalarStep.run
    dsimp only
    omega
  have hDouble : rationalWordWidth (2 : ℚ) + rationalWordWidth doubled.1 ≤ doubled.2 := by
    unfold doubled GeneralPaperRationalScalarStep.run
    dsimp only
    omega
  have hFields := fields_bound A (natBits C)
    [num.2, quotient.2, doubled.2, num.2 + quotient.2,
      num.2 + quotient.2 + doubled.2, C, A, 16 * A, 16] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A [num.2, quotient.2, doubled.2, num.2 + quotient.2,
    num.2 + quotient.2 + doubled.2, C, A, 16 * A, 16] ≤ 9 * (natBits C + A) + 32 * A at hFields
  have hBits : natBits C ≤ C + 2 := by
    have h := Nat.log2_le_self C
    change 1 + (C.log2 + 1) ≤ C + 2
    omega
  change natBits a + rationalWordWidth D + rationalWordWidth (2 : ℚ) +
    rationalWordWidth num.1 + rationalWordWidth quotient.1 + rationalWordWidth doubled.1 +
    (num.2 + quotient.2 + doubled.2) +
    fields A [num.2, quotient.2, doubled.2, num.2 + quotient.2,
      num.2 + quotient.2 + doubled.2, C, A, 16 * A, 16] + 128 * A ≤ 128 * (C + A + 1)
  omega

theorem coordinate_frame_bound (model : RationalCostModel) (A D a s : ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : a ≤ D) :
    coordinateFrame model A (D : ℚ) a ≤
      128 * (12 * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height s) + 65 * A + 65) := by
  have h := GeneralPaperEqualLengthArray.coordinate_work model A D a s hs hD ha
  exact (coordinate_frame_le model A (D : ℚ) a).trans (Nat.mul_le_mul_left 128 (by omega))

theorem coordinate_height (D a s : ℕ) (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : a ≤ D) :
    RationalHeight (2 * ((a : ℚ) / (D : ℚ))) (GeneralPaperEqualLengthArray.height s) := by
  have hA := (binaryWordWidth_mono ha).trans hD
  have hNatA := DyadicMidpointAssembly.nat_height a s (by omega)
    ((lt_pow_binaryWordWidth a).trans_le (Nat.pow_le_pow_right (by decide) hA))
  have hNatD := DyadicMidpointAssembly.nat_height D s (by omega)
    ((lt_pow_binaryWordWidth D).trans_le (Nat.pow_le_pow_right (by decide) hD))
  have hTwo : RationalHeight (2 : ℚ) s :=
    (show RationalHeight (2 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  exact (hTwo.mul (hNatA.div hNatD)).mono (by
    unfold GeneralPaperEqualLengthArray.height expressionHeightBudget
    omega)

theorem every_prefix {n : ℕ} (model : RationalCostModel) (A D s : ℕ)
    (weights : FixedArrayTable n ℕ) (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s)
    (ha : ∀ j, weights.read j ≤ D) (k : ℕ) (hk : k ≤ n) (borrowed scratch : ℕ)
    (hScratch : scratch ≤ 128 * (12 * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height s) + 65 * A + 65)) :
    window id A (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))
      rationalWordWidth k hk borrowed scratch ≤
      borrowed + arrayProfile A n (1 + 2 * GeneralPaperEqualLengthArray.height s) +
        (n + 1) * frame A n
          (PaperIndexedArrayConstruction.run id A
            (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 +
        128 * (12 * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height s) + 65 * A + 65) := by
  apply GeneralPaperIndexedArrayLifetime.window_bound id A _ rationalWordWidth _ _ _ k hk borrowed scratch hScratch
  intro j
  rw [GeneralPaperEqualLengthArray.coordinate_data]
  exact rationalWordWidth_of_height (coordinate_height D (weights.read j) s hs hD (ha j))

theorem current_callback {n : ℕ} (model : RationalCostModel) (A D s : ℕ)
    (weights : FixedArrayTable n ℕ) (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s)
    (ha : ∀ j, weights.read j ≤ D) (k : ℕ) (hk : k < n) (borrowed : ℕ) :
    window id A (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))
      rationalWordWidth k hk.le borrowed (coordinateFrame model A (D : ℚ) (weights.read ⟨k, hk⟩)) ≤
      borrowed + arrayProfile A n (1 + 2 * GeneralPaperEqualLengthArray.height s) +
        (n + 1) * frame A n
          (PaperIndexedArrayConstruction.run id A
            (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 +
        128 * (12 * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height s) + 65 * A + 65) :=
  every_prefix model A D s weights hs hD ha k hk.le borrowed _
    (coordinate_frame_bound model A D (weights.read ⟨k, hk⟩) s hs hD (ha _))

def denominatorFrame (A D : ℕ) : ℕ :=
  let actual := GeneralPaperRationalScalarStep.natural A D
  natBits D + rationalWordWidth actual.1 + natBits actual.2 + 64 * A

theorem denominator_bound (A D s : ℕ) (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) :
    denominatorFrame A D ≤ 128 * (s + A + 1) := by
  have hRat := rationalWordWidth_of_height
    (DyadicMidpointAssembly.nat_height D s (by omega)
      ((lt_pow_binaryWordWidth D).trans_le (Nat.pow_le_pow_right (by decide) hD)))
  have hNat : natBits (GeneralPaperRationalScalarStep.natural A D).2 ≤
      (GeneralPaperRationalScalarStep.natural A D).2 + 2 := by
    have h := Nat.log2_le_self (GeneralPaperRationalScalarStep.natural A D).2
    change 1 + ((GeneralPaperRationalScalarStep.natural A D).2.log2 + 1) ≤ _
    omega
  unfold denominatorFrame GeneralPaperRationalScalarStep.natural natBits
  dsimp only
  change 1 + binaryWordWidth (binaryWordWidth D + rationalWordWidth (D : ℚ) + 16 * A + 16) ≤
    binaryWordWidth D + rationalWordWidth (D : ℚ) + 16 * A + 16 + 2 at hNat
  omega

end Blotto.GeneralPaperEqualLengthLifetime
