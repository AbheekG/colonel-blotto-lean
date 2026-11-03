import Blotto.GeneralPaperEqualLengthAllocationJoin

/-! The completed length-constructor return owns its rounded input array,
converted denominator, finished output and all returned price/control fields.
This closes the return boundary left separate from active callback windows. -/
namespace Blotto.GeneralPaperEqualLengthReturnStorage
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (natBits fields fields_bound)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def returnWindow {n : ℕ} (model : RationalCostModel) (A : ℕ)
    (weights : FixedArrayTable n ℕ) (D borrowed : ℕ) : ℕ :=
  let den := GeneralPaperRationalScalarStep.natural A D
  let arr := PaperIndexedArrayConstruction.run id A
    (fun j => GeneralPaperEqualLengthArray.coordinate model A den.1 (weights.read j))
  let actual := GeneralPaperEqualLengthArray.run model A weights D
  borrowed + arrayFootprint A natBits weights + GeneralPaperEqualLengthLifetime.denominatorFrame A D +
    arrayFootprint A rationalWordWidth actual.1 +
    fields A [den.2, arr.2, den.2 + arr.2, 32 * A, actual.2] + 128 * A

def profile (model : RationalCostModel) (A n s borrowed : ℕ) : ℕ :=
  borrowed + arrayProfile A n (s + 1) + 128 * (s + A + 1) +
    arrayProfile A n (1 + 2 * GeneralPaperEqualLengthArray.height s) +
    5 * (natBits (GeneralPaperEqualLengthPhaseStorage.loopProfile model A n s) + A) + 160 * A

theorem actual {n : ℕ} (model : RationalCostModel) (A D s : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : ∀ j, weights.read j ≤ D) (borrowed : ℕ) :
    returnWindow model A weights D borrowed ≤ profile model A n s borrowed := by
  let den := GeneralPaperRationalScalarStep.natural A D
  let arr := PaperIndexedArrayConstruction.run id A
    (fun j => GeneralPaperEqualLengthArray.coordinate model A den.1 (weights.read j))
  let result := GeneralPaperEqualLengthArray.run model A weights D
  let F := GeneralPaperEqualLengthPhaseStorage.loopProfile model A n s
  have hCost : result.2 ≤ F := GeneralPaperEqualLengthArray.work model A weights D s hs hD ha
  have hTotal : result.2 = den.2 + arr.2 + 32 * A + 32 := rfl
  have hInput := array_bound A (s + 1) natBits weights (by
    intro j
    have h := (binaryWordWidth_mono (ha j)).trans hD
    unfold natBits
    omega)
  have hDen := GeneralPaperEqualLengthLifetime.denominator_bound A D s hs hD
  have hOutput := array_bound A (1 + 2 * GeneralPaperEqualLengthArray.height s) rationalWordWidth result.1 (by
    intro j
    change rationalWordWidth ((GeneralPaperEqualLengthArray.run model A weights D).1.read j) ≤ _
    rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    exact rationalWordWidth_of_height (GeneralPaperEqualLengthLifetime.coordinate_height D (weights.read j) s hs hD (ha j)))
  have hFields := fields_bound A (natBits F) [den.2, arr.2, den.2 + arr.2, 32 * A, result.2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A [den.2, arr.2, den.2 + arr.2, 32 * A, result.2] ≤ 5 * (natBits F + A) + 32 * A at hFields
  change borrowed + arrayFootprint A natBits weights + GeneralPaperEqualLengthLifetime.denominatorFrame A D +
    arrayFootprint A rationalWordWidth result.1 + fields A [den.2, arr.2, den.2 + arr.2, 32 * A, result.2] + 128 * A ≤ _
  unfold profile
  dsimp only [F] at hFields
  omega

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (borrowed : ℕ) :
    let raw := (GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values).1
    returnWindow model A raw.1 raw.2 borrowed ≤ profile model A n (binaryWordWidth n + exponent + 11) borrowed := by
  dsimp only
  have hD := GeneralPaperEqualNativeSampler.roundDen_word bits model W exponent values v hv
  apply actual model A _ _ _ (by omega) (hD.trans (by omega))
  intro j
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => (GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values).1.1.read j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact h.trans_eq (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 exponent values)

theorem profile_scale (model : RationalCostModel) (n s : ℕ) (borrowed : ℕ → ℕ)
    (hb : GeneralPaperReferenceScaling.Scale borrowed) :
    GeneralPaperReferenceScaling.Scale (fun A => profile model A n s (borrowed A)) := by
  unfold profile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

end Blotto.GeneralPaperEqualLengthReturnStorage
