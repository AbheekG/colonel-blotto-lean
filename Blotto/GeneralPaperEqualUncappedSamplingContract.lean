import Blotto.GeneralPaperEqualRejectionTraceReads

/-! The paper's native grouped equal-budget sampler in uncapped fair-bit
trace semantics: exact law, independent whole players, original-value Nash
guarantee and logarithmic expected reads. Complete preparation/cached output
and primitive bit-work resource joins remain separate. -/
namespace Blotto.GeneralPaperEqualUncappedSamplingContract
open MeasureTheory
open scoped BigOperators Classical ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualCategoricalIntegerData
open GeneralPaperEqualRejectionTraceMeasure (Trace)

theorem independent_traces {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) :
    let μ := (GeneralPaperEqualRejectionTraceMeasure.law (denominator l.weight) K
      (denominator_pos l.weight) : Measure (Trace (denominator l.weight) K))
    let f := fun trace j => (GeneralPaperEqualRejectionTraceLaw.decode G l K trace j : ℝ)
    Measure.map (Prod.map f f) (μ.prod μ) =
      (GeneralPaperEqualRejectionTraceLaw.outputLaw G l K : Measure (Allocation n)).prod
        (GeneralPaperEqualRejectionTraceLaw.outputLaw G l K : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)).symm

noncomputable def nativeLaw {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) : Mixed n :=
  GeneralPaperEqualRejectionTraceLaw.outputLaw (terminal (rounded bits model W k values v hv) small).partition
    (lottery (rounded bits model W k values v hv) small) (k + 5)

theorem nativeLaw_eq {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) :
    nativeLaw bits model W k values v hv small =
      GeneralPaperEqualFiniteKernel.law (rounded bits model W k values v hv) small k :=
  GeneralPaperEqualRejectionTraceLaw.outputLaw_eq _ _ _

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) :
    let μ := nativeLaw bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small
    Supported 1 μ ∧ regret v.values 1 μ μ ≤ (eps : ℝ) := by
  dsimp only
  rw [nativeLaw_eq]
  exact GeneralPaperEqualNativeSampler.accuracy_regret bits model W values v hv eps hp hOne small

theorem native_expected_reads {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) :
    let l := lottery (rounded bits model W k values v hv) small
    let N := denominator l.weight
    (∫⁻ trace, (GeneralPaperEqualRejectionTraceReads.reads N (k + 5) trace : ℝ≥0∞)
      ∂(GeneralPaperEqualRejectionTraceMeasure.law N (k + 5) (denominator_pos l.weight) : Measure (Trace N (k + 5)))) ≤
      ENNReal.ofReal ((33554432 : ℝ) * (binaryWordWidth n + k + 10 : ℕ)) := by
  dsimp only
  have he := GeneralPaperEqualRejectionTraceReads.expected_reads_bound
    (denominator (lottery (rounded bits model W k values v hv) small).weight) (k + 5)
    (denominator_pos (lottery (rounded bits model W k values v hv) small).weight)
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hw : (UniformNatRejection.width (denominator (lottery (rounded bits model W k values v hv) small).weight) : ℝ) ≤
      (9 * GeneralPaperEqualNativeSampler.segmentHeight n k + 1 : ℕ) := by
    have h := rejection_width (lottery (rounded bits model W k values v hv) small).weight
      (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small).1
    exact_mod_cast (h.trans_eq (by ring))
  have hb : GeneralPaperEqualNativeSampler.segmentHeight n k ≤ 524288 * (binaryWordWidth n + k + 10) := by
    unfold GeneralPaperEqualNativeSampler.segmentHeight expressionHeightBudget GeneralPaperEqualNativeSampler.fieldHeight
    norm_num
    omega
  have hb' : (GeneralPaperEqualNativeSampler.segmentHeight n k : ℝ) ≤
      524288 * (binaryWordWidth n + k + 10 : ℕ) := by exact_mod_cast hb
  push_cast at hw hb' ⊢
  have hn : (0 : ℝ) ≤ binaryWordWidth n := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith only [hw, hb', hn, hk]

theorem accuracy_expected_reads {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ)
    (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) :
    let k := (GeneralPaperDyadicAccuracy.prepare eps).exponent
    let l := lottery (rounded bits model W k values v hv) small
    let N := denominator l.weight
    (∫⁻ trace, (GeneralPaperEqualRejectionTraceReads.reads N (k + 5) trace : ℝ≥0∞)
      ∂(GeneralPaperEqualRejectionTraceMeasure.law N (k + 5) (denominator_pos l.weight) : Measure (Trace N (k + 5)))) ≤
      ENNReal.ofReal ((33554432 : ℝ) * (binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 10 : ℕ)) := by
  dsimp only
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by
    have h0 := GeneralPaperDyadicAccuracy.prepare_work eps
    have h1 := GeneralPaperDyadicAccuracy.prepare_work_exact eps
    omega
  apply (native_expected_reads bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small).trans
  apply ENNReal.ofReal_le_ofReal
  gcongr

end Blotto.GeneralPaperEqualUncappedSamplingContract
