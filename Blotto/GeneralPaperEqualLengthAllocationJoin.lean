import Blotto.GeneralPaperIndexedArrayAllocationCredit

/-! Actual length-array writes and callback scratch are covered by the full
native bit-preparation ledger. This joins one preparation phase; other phase
lifetimes and the whole common-reference/capacity join remain open. -/
namespace Blotto.GeneralPaperEqualLengthAllocationJoin
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile)
open GeneralPaperEncodedScalarStorage (natBits)
open GeneralPaperIndexedArrayLifetime (prefixTable frame)
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem scalar_written (model : RationalCostModel) (A : ℕ)
    (op : GeneralPaperRationalScalarStep.Op) (a b : ℚ) :
    rationalWordWidth (GeneralPaperRationalScalarStep.run model A op a b).1 ≤
      (GeneralPaperRationalScalarStep.run model A op a b).2 := by
  unfold GeneralPaperRationalScalarStep.run
  dsimp only
  omega

theorem coordinate_written (model : RationalCostModel) (A : ℕ) (D : ℚ) (a : ℕ) :
    rationalWordWidth (GeneralPaperEqualLengthArray.coordinate model A D a).1 ≤
      (GeneralPaperEqualLengthArray.coordinate model A D a).2 := by
  have h := scalar_written model A .mul 2
    (GeneralPaperRationalScalarStep.run model A .div (GeneralPaperRationalScalarStep.natural A a).1 D).1
  unfold GeneralPaperEqualLengthArray.coordinate
  dsimp only
  omega

theorem prefix_charged {n : ℕ} (model : RationalCostModel) (A D : ℕ) (weights : FixedArrayTable n ℕ)
    (k : ℕ) (hk : k ≤ n) :
    arrayFootprint A rationalWordWidth
      (prefixTable id A (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j)) k hk) ≤
      16 * (PaperIndexedArrayConstruction.run id A
        (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 := by
  apply GeneralPaperIndexedArrayAllocationCredit.every_prefix_charged id A 16 _ rationalWordWidth (by decide)
  intro j
  exact (coordinate_written model A (D : ℚ) (weights.read j)).trans
    (Nat.le_mul_of_pos_left _ (by decide))

theorem loop_le_constructor {n : ℕ} (model : RationalCostModel) (A D : ℕ) (weights : FixedArrayTable n ℕ) :
    (PaperIndexedArrayConstruction.run id A
      (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 ≤
      (GeneralPaperEqualLengthArray.run model A weights D).2 := by
  change _ ≤ (GeneralPaperRationalScalarStep.natural A D).2 +
    (PaperIndexedArrayConstruction.run id A
      (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 + 32 * A + 32
  omega

theorem length_le_total (w : GeneralPaperEqualCompactedPreparation.Work) (width boolean budget address controls : ℕ) :
    w.lengths ≤ GeneralPaperEqualBitPreparationLedger.total w width boolean budget address controls := by
  unfold GeneralPaperEqualBitPreparationLedger.total
  omega

theorem native_loop_covered {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv).weight j ≤ 1)
    (budget : ℚ) :
    let raw := (GeneralPaperValueRoundingPaperContract.run true model W 128 exponent values).1
    (PaperIndexedArrayConstruction.run id A
      (fun j => GeneralPaperEqualLengthArray.coordinate model A (raw.2 : ℚ) (raw.1.read j))).2 ≤
      GeneralPaperEqualBitPreparationLedger.profile model W A exponent values (rationalWordWidth budget) := by
  dsimp only
  let result := (GeneralPaperEqualAddressedPreparation.run true model W A exponent values v hv small budget).2
  have hLength := length_le_total result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2
  have hCost := GeneralPaperEqualBitPreparationLedger.bit_work model W A exponent values v hv small budget
  exact (loop_le_constructor model A _ _).trans (hLength.trans hCost)

theorem callback_window {n : ℕ} (model : RationalCostModel) (A D s F : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : ∀ j, weights.read j ≤ D)
    (hF : (PaperIndexedArrayConstruction.run id A
      (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 ≤ F)
    (k : ℕ) (hk : k < n) (borrowed : ℕ) :
    GeneralPaperEqualLengthPhaseStorage.phaseWindow model A weights D k hk borrowed ≤
      borrowed + arrayProfile A n (s + 1) + 128 * (s + A + 1) +
        16 * F + (n + 1) * frame A n F + 128 * (F + A + 1) := by
  have hInput := GeneralPaperEncodedBasisStorage.array_bound A (s + 1) natBits weights (by
    intro j
    have h := (binaryWordWidth_mono (ha j)).trans hD
    unfold natBits
    omega)
  have hDen := GeneralPaperEqualLengthLifetime.denominator_bound A D s hs hD
  have hPrefix := (prefix_charged model A D weights k hk.le).trans (Nat.mul_le_mul_left 16 hF)
  have hFrames := (GeneralPaperIndexedArrayLifetime.activation_bound id A
    (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j)) k hk.le).trans
      (Nat.mul_le_mul_left (n + 1) (GeneralPaperIndexedArrayLifetime.frame_mono A n _ F hF))
  have hCallback := (GeneralPaperIndexedArrayAllocationCredit.callback_work_charged id A
    (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j)) ⟨k, hk⟩).trans hF
  have hScratch := (GeneralPaperEqualLengthLifetime.coordinate_frame_le model A (D : ℚ) (weights.read ⟨k, hk⟩)).trans
    (Nat.mul_le_mul_left 128 (Nat.add_le_add_right (Nat.add_le_add_right hCallback A) 1))
  unfold GeneralPaperEqualLengthPhaseStorage.phaseWindow GeneralPaperIndexedArrayLifetime.window
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_left hInput borrowed) hDen) hPrefix) hFrames) hScratch

theorem native_callback_window {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (k : ℕ) (hk : k < n) (borrowed : ℕ) :
    let raw := (GeneralPaperValueRoundingPaperContract.run true model W 128 exponent values).1
    let s := binaryWordWidth n + exponent + 11
    let F := GeneralPaperEqualBitPreparationLedger.profile model W A exponent values (rationalWordWidth budget)
    GeneralPaperEqualLengthPhaseStorage.phaseWindow model A raw.1 raw.2 k hk borrowed ≤
      borrowed + arrayProfile A n (s + 1) + 128 * (s + A + 1) +
        16 * F + (n + 1) * frame A n F + 128 * (F + A + 1) := by
  dsimp only
  have hD := GeneralPaperEqualNativeSampler.roundDen_word true model W exponent values v hv
  refine callback_window model A _ _ _ _ (by omega) (hD.trans (by omega)) ?_
    (native_loop_covered model W A exponent values v hv small budget) k hk borrowed
  intro j
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => (GeneralPaperValueRoundingPaperContract.run true model W 128 exponent values).1.1.read j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact h.trans_eq (GeneralPaperValueRoundingPaperContract.source_sum true model W 128 exponent values)

end Blotto.GeneralPaperEqualLengthAllocationJoin
