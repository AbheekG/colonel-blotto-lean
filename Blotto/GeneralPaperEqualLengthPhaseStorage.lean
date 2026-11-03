import Blotto.GeneralPaperEqualLengthLifetime

/-! Own the rounded weights and once-converted denominator while the actual
length array is constructed. Every active callback cursor has a proved bound
including partial output, array frames, primitive scratch and work counters. -/
namespace Blotto.GeneralPaperEqualLengthPhaseStorage
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (natBits)
open GeneralPaperIndexedArrayLifetime (window frame)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def loopProfile (model : RationalCostModel) (A n s : ℕ) : ℕ :=
  (12 * n + 2) * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height s) +
    64 * (n + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead id A n n

theorem loop_work {n : ℕ} (model : RationalCostModel) (A D s : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : ∀ j, weights.read j ≤ D) :
    (PaperIndexedArrayConstruction.run id A
      (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 ≤
      loopProfile model A n s := by
  have h := GeneralPaperEqualLengthArray.work model A weights D s hs hD ha
  have hLocal : (PaperIndexedArrayConstruction.run id A
      (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 ≤
      (GeneralPaperEqualLengthArray.run model A weights D).2 := by
    change _ ≤ (GeneralPaperRationalScalarStep.natural A D).2 +
      (PaperIndexedArrayConstruction.run id A
        (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))).2 + 32 * A + 32
    omega
  exact hLocal.trans h

def phaseWindow {n : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable n ℕ)
    (D k : ℕ) (hk : k < n) (borrowed : ℕ) : ℕ :=
  window id A (fun j => GeneralPaperEqualLengthArray.coordinate model A (D : ℚ) (weights.read j))
    rationalWordWidth k hk.le
    (borrowed + arrayFootprint A natBits weights + GeneralPaperEqualLengthLifetime.denominatorFrame A D)
    (GeneralPaperEqualLengthLifetime.coordinateFrame model A (D : ℚ) (weights.read ⟨k, hk⟩))

def profile (model : RationalCostModel) (A n s borrowed : ℕ) : ℕ :=
  borrowed + arrayProfile A n (s + 1) + 128 * (s + A + 1) +
    arrayProfile A n (1 + 2 * GeneralPaperEqualLengthArray.height s) +
    (n + 1) * frame A n (loopProfile model A n s) +
    128 * (12 * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height s) + 65 * A + 65)

theorem actual {n : ℕ} (model : RationalCostModel) (A D s : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : ∀ j, weights.read j ≤ D)
    (k : ℕ) (hk : k < n) (borrowed : ℕ) :
    phaseWindow model A weights D k hk borrowed ≤ profile model A n s borrowed := by
  have hCurrent := GeneralPaperEqualLengthLifetime.current_callback model A D s weights hs hD ha k hk
    (borrowed + arrayFootprint A natBits weights + GeneralPaperEqualLengthLifetime.denominatorFrame A D)
  have hInput := array_bound A (s + 1) natBits weights (by
    intro j
    have h := (binaryWordWidth_mono (ha j)).trans hD
    unfold natBits
    omega)
  have hDen := GeneralPaperEqualLengthLifetime.denominator_bound A D s hs hD
  have hFrame := GeneralPaperIndexedArrayLifetime.frame_mono A n _ _ (loop_work model A D s weights hs hD ha)
  have hOwner := Nat.add_le_add (Nat.add_le_add_left hInput borrowed) hDen
  unfold phaseWindow profile
  exact hCurrent.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_right hOwner (arrayProfile A n (1 + 2 * GeneralPaperEqualLengthArray.height s)))
      (Nat.mul_le_mul_left (n + 1) hFrame)) _)

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (k : ℕ) (hk : k < n) (borrowed : ℕ) :
    let raw := (GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values).1
    phaseWindow model A raw.1 raw.2 k hk borrowed ≤
      profile model A n (binaryWordWidth n + exponent + 11) borrowed := by
  dsimp only
  have hD := GeneralPaperEqualNativeSampler.roundDen_word bits model W exponent values v hv
  apply actual model A _ _ _ (by omega) (hD.trans (by omega))
  intro j
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => (GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values).1.1.read j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact h.trans_eq (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 exponent values)

end Blotto.GeneralPaperEqualLengthPhaseStorage
