import Blotto.GeneralPaperEqualRealDraw

/-! The actual cached equal-budget real draw has the original-unit law,
bounded linear real-model work, every-output hard budgets and short rational
outputs. The same native accuracy input supplies canonical epsilon-Nash. -/
namespace Blotto.GeneralPaperEqualRealSamplingContract
open MeasureTheory
open scoped BigOperators Classical
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualRealDraw (run outputLaw inputLaw)
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem bit_real_law {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) :
    outputLaw p = GeneralPaperEqualCachedTraceLaw.outputLaw p model primitive A :=
  (GeneralPaperEqualRealDraw.outputLaw_eq p).trans (GeneralPaperEqualCachedTraceLaw.outputLaw_eq p model primitive A).symm

theorem independent_draws {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) :
    let μ := (inputLaw p : Measure (ℝ × (Fin p.midpointBits → Bool)))
    let f := fun z : ℝ × (Fin p.midpointBits → Bool) => (run p z.1 z.2).output.read
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw p : Measure (Allocation n)).prod (outputLaw p : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (GeneralPaperEqualRealDraw.measurable_run p)
    (GeneralPaperEqualRealDraw.measurable_run p)).symm

theorem native_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) (u : ℝ) (fresh : Fin (k + 5) → Bool) :
    (run (GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget) u fresh).work ≤
      1024 * (n + k + 1) := by
  have h := GeneralPaperEqualRealDraw.work (GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget) u fresh
  have hr := Nat.mul_le_mul_left 5 (GeneralPaperEqualNativeCache.compact_count
    (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small).2
  have hm := Nat.mul_le_mul_left 8 (GeneralPaperEqualNativeCache.group_count
    (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small)
  have hk : (GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget).midpointBits = k + 5 := rfl
  rw [hk] at h
  omega

theorem accuracy_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (u : ℝ) (fresh : Fin ((GeneralPaperDyadicAccuracy.prepare eps).exponent + 5) → Bool) :
    (run (GeneralPaperEqualNativeCache.prepare bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent
      values v hv small budget) u fresh).work ≤ 1024 * (n + binaryWordWidth ⌈eps⁻¹⌉₊ + 1) := by
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by
    have h0 := GeneralPaperDyadicAccuracy.prepare_work eps
    have h1 := GeneralPaperDyadicAccuracy.prepare_work_exact eps
    omega
  exact (native_work bits model W _ values v hv small budget u fresh).trans (by omega)

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    Supported (budget : ℝ) (outputLaw p) ∧ regret v.values (budget : ℝ) (outputLaw p) (outputLaw p) ≤ (eps : ℝ) := by
  dsimp only
  rw [bit_real_law _ model (fun _ => 1) 1]
  exact GeneralPaperEqualCachedTraceLaw.native_epsilon bits model W values v hv eps hp hOne small budget hB _ _

theorem native_output {n b : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 ≤ budget) (height : RationalHeight budget b) (u : ℝ) (fresh : Fin (k + 5) → Bool) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
    ∃ row : RationalResourceArray n, (run p u fresh).output.read = row.realAllocation ∧
      FullBudget (budget : ℝ) row.realAllocation ∧
      ∀ j, RationalHeight (row.allocation j) (33554432 * (b + binaryWordWidth n + k + 10)) := by
  dsimp only
  let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
  let i := (GeneralPaperEqualRealDraw.choose p u).value
  let row := (GeneralPaperEqualCachedEmission.emit p model (fun _ => 1) 1 i fresh).1
  refine ⟨row, ?_, ?_, ?_⟩
  · exact (GeneralPaperEqualRealDraw.data p u fresh).trans
      (GeneralPaperEqualRealDraw.point_eq_emit p model (fun _ => 1) 1 i fresh)
  · exact GeneralPaperEqualNativeCache.output_fullBudget bits model W k values v hv small budget hB _ _ i fresh
  · exact GeneralPaperEqualNativeCache.output_height bits model W k values v hv small budget height _ _ i fresh

end Blotto.GeneralPaperEqualRealSamplingContract
