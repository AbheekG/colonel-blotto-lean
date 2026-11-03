import Blotto.GeneralPaperUniformListAlgorithmContract

/-! The current paper's first value rounding for the equal-budget branch:
scale 256*n*2^k, with the midpoint exponent still k+5. The older c=128
results remain separate, and are used only for compatible size bounds. -/
namespace Blotto.GeneralPaperEqualFirstRounding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def rounded {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    RationalFieldSelector n :=
  let raw := (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv
  GeneralPaperNativeRationalValues.selector raw.2 hp.1 raw.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values)

theorem scale_successor (n k : ℕ) :
    GeneralPaperValueRoundingPaperContract.scale 256 n k =
      GeneralPaperValueRoundingPaperContract.scale 128 n (k+1) := by
  unfold GeneralPaperValueRoundingPaperContract.scale
  rw [pow_succ]
  ring

theorem source_successor {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) :
    (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1 =
      (GeneralPaperValueRoundingPaperContract.run bits model W 128 (k+1) values).1 := by
  rw [GeneralPaperValueRoundingPaperContract.data, GeneralPaperValueRoundingPaperContract.data, scale_successor]

theorem rounded_successor {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    rounded bits model W k values v hv = GeneralPaperEqualNativeSampler.rounded bits model W (k+1) values v hv := by
  have hs := source_successor bits model W k values
  have hWeight : (rounded bits model W k values v hv).weight =
      (GeneralPaperEqualNativeSampler.rounded bits model W (k+1) values v hv).weight := by
    funext j
    exact congrArg (fun raw : FixedArrayTable n ℕ × ℕ => (raw.1.read j : ℚ)/raw.2) hs
  generalize rounded bits model W k values v hv = a at hWeight ⊢
  generalize GeneralPaperEqualNativeSampler.rounded bits model W (k+1) values v hv = b at hWeight ⊢
  cases a
  cases b
  congr 1

theorem distance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    GeneralPaperValuePerturbation.distance v.values (rounded bits model W k values v hv).values ≤
      (1/(2 : ℝ)^k)/128 :=
  GeneralPaperRoundedValuePerturbation.original_distance bits model W k values v hv

theorem denominator_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    binaryWordWidth (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2 ≤
      binaryWordWidth n+k+10 := by
  rw [source_successor]
  exact (GeneralPaperEqualNativeSampler.roundDen_word bits model W (k+1) values v hv).trans_eq (by omega)

theorem lattice {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (j : Fin n) :
    OnRationalLattice (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2
      ((rounded bits model W k values v hv).weight j) :=
  GeneralPaperEqualNativeSampler.fraction_lattice _ _

end Blotto.GeneralPaperEqualFirstRounding
