import Blotto.GeneralPaperOriginalExactBitHeadlines

/-! Actual row/shift controls and their paper epsilon bounds. Direct
identity descriptions have one shift; all counts remain powers of two.
Trajectory bounds refer to the full pre-update stored row count. -/
namespace Blotto.GeneralPaperExactSamplerCounts
open GeneralPaperOriginalDrawEquilibrium GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive exponent_exact)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem made_shifts {n T K : ℕ} (price index : ℕ → ℕ) (A R k : ℕ) (hT : T = 2 ^ R)
    (o : GeneralPaperReducedValuesDriver.Output n) (hRep : GeneralPaperNativeReductionShape.ReplacedShape o)
    (hNo : GeneralPaperUnreplacedShape.Shape o) (hR : 0 < o.representatives) (b : ℚ)
    (physical : Columns T o.m K) :
    GeneralPaperExactStoredSampler.shifts
      (⟨o, b, GeneralPaperSamplingControls.specification T R k hT,
        (make price index A o hRep hNo hR physical).1⟩ : Sampler n T K) =
      if o.replaced then GeneralPaperNativeSelectedSecurity.count k else 1 := by
  by_cases h : o.replaced = true
  · rw [make_circle price index A o hRep hNo hR physical h (hRep h).1]
    simp only [GeneralPaperExactStoredSampler.shifts, GeneralPaperSamplingControls.specification, h, ↓reduceIte]
  · have hf : o.replaced = false := by cases he : o.replaced <;> simp_all
    rw [make_direct price index A o hRep hNo hR physical hf (hNo hf).1]
    simp only [GeneralPaperExactStoredSampler.shifts, hf, Bool.false_eq_true, ↓reduceIte]

theorem native_controls {n : ℕ} (model : RationalCostModel) (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) :
    let actual := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∀ sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler = some sampler →
      sampler.controls.rows = t.rows ∧ sampler.controls.rowBits = t.rowBits ∧
      sampler.controls.shiftBits = k + 6 ∧
      sampler.controls.shifts = GeneralPaperNativeSelectedSecurity.count k ∧
      GeneralPaperExactStoredSampler.shifts sampler =
        if o.replaced then GeneralPaperNativeSelectedSecurity.count k else 1 := by
  dsimp only
  intro sampler hSampler
  obtain ⟨physical, hView⟩ := GeneralPaperNativeSamplerViewAndLaw.native_view model Wv Ws Ap words values v hv b hb
  have he := Option.some.inj (hSampler.symm.trans hView)
  subst sampler
  exact ⟨rfl, rfl, rfl, rfl, made_shifts _ _ _ _ _ _ _ _ _ _ _ _⟩

theorem shift_bound (p : Problem) (hOne : epsilon p < 1) :
    (GeneralPaperNativeSelectedSecurity.count (exponent p) : ℚ) ≤ 128 / epsilon p := by
  have hp : (2 : ℚ) ^ exponent p ≤ 2 / epsilon p := by
    rw [exponent_exact p]
    exact GeneralPaperRealHeadlineParameters.power_bound (epsilon p) (epsilon_positive p) hOne
  have h := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℚ) ≤ 64)
  unfold GeneralPaperNativeSelectedSecurity.count
  push_cast
  exact h.trans_eq (by ring)

theorem trajectory_bound (model : RationalCostModel) (p : Problem) (hOne : epsilon p < 1) :
    ((GeneralPaperTrajectoryParameters.prepare
      (GeneralPaperProxyParameters.alphabet (reduced model p).m (exponent p)).lambda (exponent p)).rows : ℚ) ≤
      ((2 ^ 68 * 296 : ℕ) : ℚ) * GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p) /
        epsilon p ^ 3 * (binaryWordWidth (p.n + 4) : ℚ) := by
  have hE := epsilon_positive p
  let N := GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)
  let m := (reduced model p).m
  let k := exponent p
  have hN : 1 ≤ N := GeneralPaperRealHeadlineParameters.nstar_positive p.n p.selector.fields_positive
    (epsilon p) (epsilon_positive p) hOne
  have hm : (m : ℚ) ≤ 36 * N := by
    have h := GeneralPaperOriginalSourceValueContract.dyadic_field_count false model 1 (epsilon p)
      (epsilon_positive p) hOne p.values p.selector p.correct
    rw [← exponent_exact p] at h
    exact h
  have hmN : (m : ℚ) + 1 ≤ 37 * N := by linarith only [hm, hN]
  have hmCount : m ≤ p.n := (GeneralPaperOriginalValueReduction.count_bounds false model 1 k p.values p.selector p.correct).2.1
  have hW : binaryWordWidth (m + 3) ≤ binaryWordWidth (p.n + 4) := binaryWordWidth_mono (by omega)
  have hp : (2 : ℚ) ^ k ≤ 2 / epsilon p := by
    dsimp only [k]
    rw [exponent_exact p]
    exact GeneralPaperRealHeadlineParameters.power_bound (epsilon p) (epsilon_positive p) hOne
  have hRows : ((GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows : ℚ) ≤
      (2 : ℚ) ^ 68 * ((m : ℚ) + 1) * ((2 : ℚ) ^ k) ^ 3 * (binaryWordWidth (m + 3) : ℚ) := by
    exact_mod_cast GeneralPaperDescriptionSourceParameters.rows m k
  calc
    _ ≤ (2 : ℚ) ^ 68 * ((m : ℚ) + 1) * ((2 : ℚ) ^ k) ^ 3 * (binaryWordWidth (m + 3) : ℚ) := hRows
    _ ≤ (2 : ℚ) ^ 68 * (37 * N) * (2 / epsilon p) ^ 3 * (binaryWordWidth (p.n + 4) : ℚ) := by
      gcongr
    _ = _ := by dsimp only [N]; push_cast; ring

theorem at_word_counts (model : RationalCostModel) (W : ℕ) (p : Problem) (hOne : epsilon p < 1) :
    let actual := GeneralPaperArbitraryPreparationDraw.returned model W p
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∀ sampler : Sampler p.n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler = some sampler →
      (sampler.controls.rows : ℚ) ≤ ((2 ^ 68 * 296 : ℕ) : ℚ) *
        GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p) / epsilon p ^ 3 * (binaryWordWidth (p.n + 4) : ℚ) ∧
      (GeneralPaperExactStoredSampler.shifts sampler : ℚ) ≤ 128 / epsilon p ∧
      (o.replaced = false → GeneralPaperExactStoredSampler.shifts sampler = 1) ∧
      ∃ R L : ℕ, sampler.controls.rows = 2 ^ R ∧ GeneralPaperExactStoredSampler.shifts sampler = 2 ^ L := by
  dsimp only
  intro sampler hSampler
  have hc := native_controls model W W W p.words p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hr := GeneralPaperArbitraryPreparationDraw.returned_reduced model W p
  have hk := GeneralPaperArbitraryPreparationDraw.returned_exponent model W p
  have hRows := congrArg₂ (fun (o : GeneralPaperReducedValuesDriver.Output p.n) (k : ℕ) =>
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows) hr hk
  have hRowEq := hc.1.trans hRows
  have hCast : (sampler.controls.rows : ℚ) =
      ((GeneralPaperTrajectoryParameters.prepare
        (GeneralPaperProxyParameters.alphabet (reduced model p).m (exponent p)).lambda (exponent p)).rows : ℚ) := by
    exact_mod_cast hRowEq
  have hShiftEq := hc.2.2.2.1.trans (congrArg GeneralPaperNativeSelectedSecurity.count hk)
  have hShift := (GeneralPaperExactStoredSampler.shift_count_le sampler).trans_eq hShiftEq
  have hShiftQ : (GeneralPaperExactStoredSampler.shifts sampler : ℚ) ≤
      (GeneralPaperNativeSelectedSecurity.count (exponent p) : ℚ) := by exact_mod_cast hShift
  refine ⟨hCast.le.trans (trajectory_bound model p hOne), hShiftQ.trans (shift_bound p hOne), ?_,
    sampler.controls.rowBits, GeneralPaperExactStoredSampler.shiftBits sampler,
    sampler.controls.rows_power, GeneralPaperExactStoredSampler.shifts_power sampler⟩
  intro hFalse
  dsimp only [GeneralPaperArbitraryPreparationDraw.returned] at hFalse
  set_option backward.isDefEq.respectTransparency false in
    simpa only [hFalse, Bool.false_eq_true, ↓reduceIte] using hc.2.2.2.2

end Blotto.GeneralPaperExactSamplerCounts
