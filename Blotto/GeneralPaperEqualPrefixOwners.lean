import Blotto.GeneralPaperSegmentFactoryReferenceScaling

/-! Original and rounded input owners retained by the equal preparation
caller. Original rational encoding is additive; short rounded integers and
lengths use the common denominator word. These are erased owner observers. -/
namespace Blotto.GeneralPaperEqualPrefixOwners
open scoped BigOperators
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem original_exact {n : ℕ} (A : ℕ) (values : FixedArrayTable n ℚ) :
    arrayFootprint A rationalWordWidth values = GeneralPaperValueRoundingInputPrice.inputSize values + n * A + 64 * A := by
  unfold arrayFootprint GeneralPaperValueRoundingInputPrice.inputSize
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

def roundedFoot {n : ℕ} (A : ℕ) (weights : FixedArrayTable n ℕ) (D : ℕ) : ℕ :=
  arrayFootprint A natBits weights + natBits D + 64 * A

def roundedProfile (A n s : ℕ) : ℕ := arrayProfile A n (s + 1) + (s + 1) + 64 * A

theorem rounded_bound {n : ℕ} (A s : ℕ) (weights : FixedArrayTable n ℕ) (D : ℕ)
    (hD : binaryWordWidth D ≤ s) (hWeights : ∀ j, weights.read j ≤ D) :
    roundedFoot A weights D ≤ roundedProfile A n s := by
  have hArray := array_bound A (s + 1) natBits weights (by
    intro j
    have h := (binaryWordWidth_mono (hWeights j)).trans hD
    unfold natBits
    omega)
  have hScalar : natBits D ≤ s + 1 := by unfold natBits; omega
  unfold roundedFoot roundedProfile
  omega

theorem native_rounded {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    let raw := (GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values).1
    roundedFoot A raw.1 raw.2 ≤ roundedProfile A n (binaryWordWidth n + exponent + 9) := by
  dsimp only
  apply rounded_bound A _ _ _ (GeneralPaperEqualNativeSampler.roundDen_word bits model W exponent values v hv)
  intro j
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => (GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values).1.1.read j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact h.trans_eq (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 exponent values)

theorem native_lengths {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small))
    (lengths : FixedArrayTable n ℚ)
    (hLength : ∀ j, lengths.read j = (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).length j) :
    arrayFootprint A rationalWordWidth lengths ≤ arrayProfile A n (1 + 2 * (binaryWordWidth n + exponent + 9)) :=
  array_bound A _ rationalWordWidth lengths (fun j => rationalWordWidth_of_height
    ((GeneralPaperEqualNativeRouteCost.fields_height bits model W exponent values v hv small p lengths hLength).1 j))

end Blotto.GeneralPaperEqualPrefixOwners
