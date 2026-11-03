import Blotto.GeneralPaperEqualFirstInitialPrefixLifetime

/-! Structural source facts for the corrected bit-space analysis. Source
heights use the successor size bound; prepared midpoint precision remains k+5.
These are erased proofs for the actual c=256 returned weights. -/
namespace Blotto.GeneralPaperEqualFirstNativeFacts
open GeneralPaperEqualFiniteKernel (spec lottery)
set_option autoImplicit false

abbrev rounded := @GeneralPaperEqualFirstRounding.rounded

def roundDen {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) : ℕ :=
  (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2

theorem roundDen_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    0 < roundDen bits model W k values :=
  (GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv).1

theorem roundDen_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    binaryWordWidth (roundDen bits model W k values) ≤ binaryWordWidth n+k+10 :=
  GeneralPaperEqualFirstRounding.denominator_word bits model W k values v hv

abbrev fraction_lattice := GeneralPaperEqualNativeSampler.fraction_lattice

theorem rounded_lattice {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (j : Fin n) : OnRationalLattice (roundDen bits model W k values) ((rounded bits model W k values v hv).weight j) :=
  GeneralPaperEqualFirstRounding.lattice bits model W k values v hv j

def fieldHeight (n k : ℕ) : ℕ := 2*(binaryWordWidth n+k+10)+1
def segmentHeight (n k : ℕ) : ℕ := expressionHeightBudget (fieldHeight n k) 18

theorem native_spec_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1) :
    (spec (rounded bits model W k values v hv) small).FieldsHeight (fieldHeight n k) := by
  have h := GeneralPaperEqualNativeSampler.unit_spec_height (rounded bits model W k values v hv) small
    (roundDen bits model W k values) (roundDen_positive bits model W k values v hv)
    (rounded_lattice bits model W k values v hv)
  apply h.mono
  have hw := roundDen_word bits model W k values v hv
  unfold fieldHeight
  omega

theorem native_lottery_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1) :
    (lottery (rounded bits model W k values v hv) small).HeightAt (segmentHeight n k) := by
  have h := GeneralPaperEqualFirstHeights.lottery_height bits model W k values v hv small
  convert h using 1
  simp only [segmentHeight, fieldHeight, GeneralPaperEqualNativeSampler.segmentHeight,
    GeneralPaperEqualNativeSampler.fieldHeight, Nat.add_assoc]

end Blotto.GeneralPaperEqualFirstNativeFacts
