import Blotto.GeneralPaperEqualRejectionAllocation
import Blotto.PreparedGroupHeight
import Blotto.RationalUnitLatticeHeight
import Blotto.RationalGroupProgramHeight

/-! Concrete short heights and expected fair-bit bounds for the paper's
native positive-rounded equal-budget grouped sampler. Lattice invariants
bound group sums independently of n; all source denominators and segment
heights are derived from the actual c=128 rounding return. -/
namespace Blotto.GeneralPaperEqualNativeSampler
open MeasureTheory
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperEqualFiniteKernel (terminal spec lottery)
open GeneralPaperEqualCategoricalIntegerData

def rounded {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    RationalFieldSelector n :=
  let raw := (GeneralPaperValueRoundingPaperContract.run bits model W 128 k values).1
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 128 k (by decide) values v hv
  GeneralPaperNativeRationalValues.selector raw.2 hp.1 raw.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 k values)

theorem rounded_eq {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    rounded bits model W k values v hv = GeneralPaperEqualRoundedBoundary.rounded bits model W k values v hv := rfl

def roundDen {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) : ℕ :=
  (GeneralPaperValueRoundingPaperContract.run bits model W 128 k values).1.2

theorem roundDen_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    0 < roundDen bits model W k values :=
  (GeneralPaperValueRoundingPaperContract.positivity bits model W 128 k (by decide) values v hv).1

theorem roundDen_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    binaryWordWidth (roundDen bits model W k values) ≤ binaryWordWidth n + k + 9 := by
  have hd := (GeneralPaperValueRoundingPaperContract.denominator bits model W 128 k values v hv).2.le
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hb : roundDen bits model W k values ≤ 129 * n * 2 ^ k := by
    unfold GeneralPaperValueRoundingPaperContract.scale at hd
    change roundDen bits model W k values ≤ 128 * n * 2 ^ k + n at hd
    nlinarith only [hd, Nat.mul_le_mul_left n hp]
  have h0 := binaryWordWidth_mono hb
  have h1 := binaryWordWidth_mul (129 * n) (2 ^ k)
  have h2 := binaryWordWidth_mul 129 n
  have h129 : binaryWordWidth 129 = 8 := by decide
  have hPow : binaryWordWidth (2 ^ k) = k + 1 := by simp only [binaryWordWidth, Nat.log2_two_pow]
  rw [h129] at h2
  rw [hPow] at h1
  omega

theorem fraction_lattice (a D : ℕ) : OnRationalLattice D ((a : ℚ) / D) := by
  have h := Rat.den_dvd (a : ℤ) (D : ℤ)
  rw [Rat.divInt_eq_div] at h
  change ((↑a / ↑D : ℚ).den : ℤ) ∣ (D : ℤ) at h
  exact_mod_cast h

theorem rounded_lattice {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (j : Fin n) : OnRationalLattice (roundDen bits model W k values)
      ((rounded bits model W k values v hv).weight j) :=
  fraction_lattice _ _

theorem unit_spec_height {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (D : ℕ) (hD : 0 < D) (hl : ∀ j, OnRationalLattice D (v.weight j)) :
    (spec v small).FieldsHeight (2 * binaryWordWidth D + 1) := by
  let i := terminal v small
  let p := RationalTerminalPacking.prepare i
  have hL : ∀ j, OnRationalLattice D (i.partition.length j) := by
    intro j
    exact (hl j).int_mul 2
  constructor
  · change RationalHeight (1 : ℚ) (2 * binaryWordWidth D + 1)
    have hWord : 0 < binaryWordWidth D := by unfold binaryWordWidth; omega
    exact (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono (by omega)
  · intro g
    have ht := rationalHeight_unit_lattice hD (i.partition.total_on_lattice D hL g)
      ⟨(i.partition.total_pos g).le, i.partition_total_le g⟩
    change RationalHeight (p.groups.read g).2 (2 * binaryWordWidth D + 1)
    rw [p.total_correct]
    exact ht.mono (by omega)

def fieldHeight (n k : ℕ) : ℕ := 2 * (binaryWordWidth n + k + 9) + 1
def segmentHeight (n k : ℕ) : ℕ := expressionHeightBudget (fieldHeight n k) 18

theorem native_spec_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) :
    (spec (rounded bits model W k values v hv) small).FieldsHeight (fieldHeight n k) := by
  have h := unit_spec_height (rounded bits model W k values v hv) small
    (roundDen bits model W k values) (roundDen_positive bits model W k values v hv)
    (rounded_lattice bits model W k values v hv)
  apply h.mono
  have hw := roundDen_word bits model W k values v hv
  unfold fieldHeight
  omega

theorem native_lottery_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) :
    (lottery (rounded bits model W k values v hv) small).HeightAt (segmentHeight n k) :=
  (native_spec_height bits model W k values v hv small).lottery
    (by unfold fieldHeight; omega) (terminal (rounded bits model W k values v hv) small).groups_count

def draw {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (cap : ℕ) :=
  GeneralPaperEqualRejectionAllocation.run
    (terminal (rounded bits model W k values v hv) small).partition
    (lottery (rounded bits model W k values v hv) small) cap (k + 5)

theorem expected_bits {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (cap : ℕ) :
    let l := lottery (rounded bits model W k values v hv) small
    (fairBitKernel (cap * UniformNatRejection.width (denominator l.weight) + (k + 5))).mean
      (fun fresh => ((draw bits model W k values v hv small cap fresh).reads : ℝ)) ≤
        (33554432 : ℝ) * (binaryWordWidth n + k + 10 : ℕ) := by
  dsimp only
  have h := GeneralPaperEqualRejectionAllocation.expected_reads_height
    (terminal (rounded bits model W k values v hv) small).partition
    (lottery (rounded bits model W k values v hv) small)
    (native_lottery_height bits model W k values v hv small).1 cap (k + 5)
  have hb : segmentHeight n k ≤ 524288 * (binaryWordWidth n + k + 10) := by
    unfold segmentHeight expressionHeightBudget fieldHeight
    norm_num
    omega
  have hb' : (segmentHeight n k : ℝ) ≤ 524288 * (binaryWordWidth n + k + 10 : ℕ) := by exact_mod_cast hb
  push_cast at hb'
  push_cast at h
  change (fairBitKernel _).mean _ ≤ _
  push_cast
  dsimp only [draw]
  have hn : (0 : ℝ) ≤ binaryWordWidth n := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith only [h, hb', hn, hk]

theorem completed_fullBudget {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (cap : ℕ)
    (fresh : Fin (cap * UniformNatRejection.width
      (denominator (lottery (rounded bits model W k values v hv) small).weight) + (k + 5)) → Bool)
    (row : Fin n → ℚ) (h : (draw bits model W k values v hv small cap fresh).output = some row) :
    FullBudget 1 (fun j => (row j : ℝ)) := by
  have hb : ∀ slot, FullBudget ((1 : ℚ) : ℝ)
      ((lottery (rounded bits model W k values v hv) small).real.P slot) ∧
      FullBudget ((1 : ℚ) : ℝ) ((lottery (rounded bits model W k values v hv) small).real.Q slot) := by
    simpa only [Rat.cast_one] using GeneralPaperEqualFiniteKernel.endpoints
      (rounded bits model W k values v hv) small
  simpa only [Rat.cast_one] using GeneralPaperEqualRejectionAllocation.completed_fullBudget
    (terminal (rounded bits model W k values v hv) small).partition
    (lottery (rounded bits model W k values v hv) small) cap (k + 5) 1 hb fresh row h

theorem completed_law_tends {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1)
    (A : Set (Allocation n)) (hA : MeasurableSet A) :
    Filter.Tendsto (fun cap =>
      (fairBitKernel (cap * UniformNatRejection.width
        (denominator (lottery (rounded bits model W k values v hv) small).weight) + (k + 5))).mean
        (fun fresh => match (draw bits model W k values v hv small cap fresh).output with
          | none => 0 | some row => if (fun j => (row j : ℝ)) ∈ A then (1 : ℝ) else 0))
      Filter.atTop (nhds ((GeneralPaperEqualFiniteKernel.law
        (rounded bits model W k values v hv) small k : Measure (Allocation n)).real A)) :=
  GeneralPaperEqualRejectionAllocation.completed_event_tends
    (terminal (rounded bits model W k values v hv) small).partition
    (lottery (rounded bits model W k values v hv) small) (k + 5) A hA

theorem original_regret {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) :
    let law := GeneralPaperEqualFiniteKernel.law (rounded bits model W k values v hv) small k
    Supported 1 law ∧ regret v.values 1 law law ≤ 3 * (1 / (2 : ℝ) ^ k) / 32 := by
  dsimp only
  have hr := GeneralPaperEqualFiniteKernel.regrets (rounded bits model W k values v hv) small k
  have hd := GeneralPaperEqualRoundedBoundary.distance bits model W k values v hv
  change GeneralPaperValuePerturbation.distance v.values
    (rounded bits model W k values v hv).values ≤ (1 / (2 : ℝ) ^ k) / 64 at hd
  have ht := GeneralPaperValuePerturbation.regret_le_shift v.values
    (rounded bits model W k values v hv).values 1 (by norm_num)
    (GeneralPaperEqualFiniteKernel.law (rounded bits model W k values v hv) small k)
    (GeneralPaperEqualFiniteKernel.law (rounded bits model W k values v hv) small k)
  refine ⟨hr.1, ?_⟩
  have he : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ k := by positivity
  linarith only [hr.2, hd, ht, he]

theorem accuracy_expected_bits {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ)
    (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (cap : ℕ) :
    let k := (GeneralPaperDyadicAccuracy.prepare eps).exponent
    let l := lottery (rounded bits model W k values v hv) small
    (fairBitKernel (cap * UniformNatRejection.width (denominator l.weight) + (k + 5))).mean
      (fun fresh => ((draw bits model W k values v hv small cap fresh).reads : ℝ)) ≤
        (33554432 : ℝ) * (binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 10 : ℕ) := by
  dsimp only
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by
    have h0 := GeneralPaperDyadicAccuracy.prepare_work eps
    have h1 := GeneralPaperDyadicAccuracy.prepare_work_exact eps
    omega
  have h := expected_bits bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small cap
  apply h.trans
  gcongr

theorem accuracy_regret {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) :
    let k := (GeneralPaperDyadicAccuracy.prepare eps).exponent
    let law := GeneralPaperEqualFiniteKernel.law (rounded bits model W k values v hv) small k
    Supported 1 law ∧ regret v.values 1 law law ≤ (eps : ℝ) := by
  dsimp only
  have h := original_regret bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small
  have he := (GeneralPaperDyadicAccuracy.accuracy_bounds eps hp hOne).2
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at he
  have he' : (1 / (2 : ℝ) ^ (GeneralPaperDyadicAccuracy.prepare eps).exponent) ≤ (eps : ℝ) := by
    have hr : (((1 / (2 : ℚ) ^ (GeneralPaperDyadicAccuracy.prepare eps).exponent : ℚ) : ℝ)) ≤
        (eps : ℝ) := by exact_mod_cast he
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hr
  have hep : (0 : ℝ) < eps := by exact_mod_cast hp
  refine ⟨h.1, ?_⟩
  linarith only [h.2, he', hep]

end Blotto.GeneralPaperEqualNativeSampler
