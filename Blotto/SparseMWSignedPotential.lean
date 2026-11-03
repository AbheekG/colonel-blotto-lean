import Blotto.SparseMWSharpPotential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Signed-loss shifts preserve the actual normalized entropy update and
regret pairings. The proved interval bound has coefficient one-half times
the squared range. The sharp one-half squared supnorm bound below is derived
from the finite tilted-variance Hoeffding argument used for the source's
proof-only auxiliary noise sequence. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

theorem normalizer_shift {n : ℕ} (probability loss : Fin n → ℝ) (eta shift : ℝ) :
    normalizer probability (fun i => loss i + shift) eta =
      Real.exp (-eta * shift) * normalizer probability loss eta := by
  unfold normalizer
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : -eta * (loss i + shift) = -eta * shift + -eta * loss i := by ring_nf
  rw [he, Real.exp_add]
  ring_nf

theorem normalizedUpdate_shift {n : ℕ} (probability loss : Fin n → ℝ) (eta shift : ℝ) :
    normalizedUpdate probability (fun i => loss i + shift) eta = normalizedUpdate probability loss eta := by
  funext i
  unfold normalizedUpdate
  rw [normalizer_shift]
  have he : -eta * (loss i + shift) = -eta * shift + -eta * loss i := by ring_nf
  rw [he, Real.exp_add]
  have hmul : probability i * (Real.exp (-eta * shift) * Real.exp (-eta * loss i)) =
      Real.exp (-eta * shift) * (probability i * Real.exp (-eta * loss i)) := by ring_nf
  rw [hmul, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

theorem regret_pairing_shift {n : ℕ} (probability comparator loss : Fin n → ℝ) (shift : ℝ)
    (hp : ∑ i, probability i = 1) (hu : ∑ i, comparator i = 1) :
    (∑ i, (probability i - comparator i) * (loss i + shift)) =
      ∑ i, (probability i - comparator i) * loss i := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hp, hu, sub_self, zero_mul, add_zero]

theorem relativeEntropy_step_interval {n : ℕ} (comparator probability loss : Fin n → ℝ)
    (eta lower upper : ℝ) (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (hu : ∑ i, comparator i = 1) (heta : 0 ≤ eta)
    (hl : ∀ i, lower ≤ loss i ∧ loss i ≤ upper) :
    eta * (∑ i, (probability i - comparator i) * loss i) ≤
      relativeEntropy comparator probability - relativeEntropy comparator (normalizedUpdate probability loss eta) +
        (eta ^ 2 / 2) * (upper - lower) ^ 2 := by
  have he := relativeEntropy_step_sharp comparator probability (fun i => loss i - lower) eta
    hp hs hu heta (fun i => sub_nonneg.mpr (hl i).1)
  have hupdate : normalizedUpdate probability (fun i => loss i - lower) eta = normalizedUpdate probability loss eta :=
    normalizedUpdate_shift probability loss eta (-lower)
  rw [hupdate] at he
  have hpairs : (∑ i, (probability i - comparator i) * (loss i - lower)) =
      ∑ i, (probability i - comparator i) * loss i :=
    regret_pairing_shift probability comparator loss (-lower) hs hu
  rw [hpairs] at he
  have hm : (∑ i, probability i * (loss i - lower) ^ 2) ≤ (upper - lower) ^ 2 := by
    calc
      _ ≤ ∑ i, probability i * (upper - lower) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hb : (loss i - lower) ^ 2 ≤ (upper - lower) ^ 2 := by nlinarith [(hl i).1, (hl i).2]
        exact mul_le_mul_of_nonneg_left hb (hp i).le
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  have hmul := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ eta ^ 2 / 2)
  linarith

theorem finite_signed_interval_regret {n : ℕ} (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ) (lower upper : ℕ → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (heta : 0 ≤ eta) (hl : ∀ t i, lower t ≤ loss t i ∧ loss t i ≤ upper t)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      relativeEntropy comparator (probability 0) +
        (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, (upper t - lower t) ^ 2) := by
  have htelescope : ∀ T,
      eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
        relativeEntropy comparator (probability 0) - relativeEntropy comparator (probability T) +
          (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, (upper t - lower t) ^ 2) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have he := relativeEntropy_step_interval comparator (probability T) (loss T) eta (lower T) (upper T)
        (hp T) (hs T) hsu heta (hl T)
      rw [← hstep T] at he
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith
  have he := htelescope T
  have hn := relativeEntropy_nonnegative comparator (probability T) hu hsu (hp T) (hs T)
  linarith

theorem finite_uniform_signed_interval_regret {n : ℕ} (hn : 0 < n) (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ) (lower upper : ℕ → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (hstart : probability 0 = fun _ => 1 / (n : ℝ))
    (heta : 0 ≤ eta) (hl : ∀ t i, lower t ≤ loss t i ∧ loss t i ≤ upper t)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      Real.log n + (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, (upper t - lower t) ^ 2) := by
  have he := finite_signed_interval_regret comparator probability loss eta lower upper hu hsu hp hs heta hl hstep T
  rw [hstart] at he
  have hb := relativeEntropy_uniform_bound hn comparator hu hsu
  linarith

/- The tilted-law variance algebra needed by the sharp Hoeffding route.
The weights may be any nonnegative normalized finite law, including a law
obtained by positive exponential tilting. -/
theorem bounded_variance_interval {n : ℕ} (probability value : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ probability i) (hs : ∑ i, probability i = 1)
    (lower upper : ℝ) (hv : ∀ i, lower ≤ value i ∧ value i ≤ upper) :
    (∑ i, probability i * value i ^ 2) - (∑ i, probability i * value i) ^ 2 ≤
      (upper - lower) ^ 2 / 4 := by
  let mean := ∑ i, probability i * value i
  have hpoint : ∀ i, value i ^ 2 ≤ (lower + upper) * value i - lower * upper := by
    intro i
    nlinarith [(hv i).1, (hv i).2]
  have hmoment : (∑ i, probability i * value i ^ 2) ≤
      (lower + upper) * mean - lower * upper := by
    calc
      _ ≤ ∑ i, probability i * ((lower + upper) * value i - lower * upper) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp i))
      _ = _ := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        rw [hs, one_mul]
        unfold mean
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring_nf
  change (∑ i, probability i * value i ^ 2) - mean ^ 2 ≤ _
  nlinarith [sq_nonneg (mean - (lower + upper) / 2)]

noncomputable def tiltedMoment {n : ℕ} (probability value : Fin n → ℝ) (order : ℕ) (t : ℝ) : ℝ :=
  ∑ i, probability i * value i ^ order * Real.exp (t * value i)

theorem tiltedMoment_zero_positive {n : ℕ} (probability value : Fin n → ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1) (t : ℝ) :
    0 < tiltedMoment probability value 0 t := by
  simpa only [tiltedMoment, pow_zero, mul_one, normalizer, neg_mul, mul_neg, neg_neg] using
    (normalizer_positive probability (fun i => -value i) t hp hs)

theorem tiltedMoment_derivative {n : ℕ} (probability value : Fin n → ℝ) (order : ℕ) (t : ℝ) :
    HasDerivAt (tiltedMoment probability value order) (tiltedMoment probability value (order + 1) t) t := by
  unfold tiltedMoment
  apply HasDerivAt.fun_sum
  intro i _
  have he := ((hasDerivAt_id t).mul_const (value i)).exp.const_mul (probability i * value i ^ order)
  convert he using 1
  · rfl
  · simp only [id_eq, one_mul]
    rw [pow_succ]
    ring_nf

noncomputable def tiltedMean {n : ℕ} (probability value : Fin n → ℝ) (t : ℝ) : ℝ :=
  tiltedMoment probability value 1 t / tiltedMoment probability value 0 t

noncomputable def tiltedVariance {n : ℕ} (probability value : Fin n → ℝ) (t : ℝ) : ℝ :=
  tiltedMoment probability value 2 t / tiltedMoment probability value 0 t - tiltedMean probability value t ^ 2

theorem tiltedMean_derivative {n : ℕ} (probability value : Fin n → ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1) (t : ℝ) :
    HasDerivAt (tiltedMean probability value) (tiltedVariance probability value t) t := by
  have he := (tiltedMoment_derivative probability value 1 t).div
    (tiltedMoment_derivative probability value 0 t) (ne_of_gt (tiltedMoment_zero_positive probability value hp hs t))
  convert he using 1
  · rfl
  · unfold tiltedVariance tiltedMean
    rw [div_pow]
    have hZ := ne_of_gt (tiltedMoment_zero_positive probability value hp hs t)
    have hfirst : tiltedMoment probability value 2 t / tiltedMoment probability value 0 t =
        (tiltedMoment probability value 2 t * tiltedMoment probability value 0 t) /
          (tiltedMoment probability value 0 t) ^ 2 := by
      rw [pow_two, mul_div_mul_right _ _ hZ]
    rw [hfirst]
    rw [← sub_div]
    congr 1
    ring_nf

theorem tiltedVariance_bound {n : ℕ} (probability value : Fin n → ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (lower upper t : ℝ) (hv : ∀ i, lower ≤ value i ∧ value i ≤ upper) :
    tiltedVariance probability value t ≤ (upper - lower) ^ 2 / 4 := by
  let weights := fun i => probability i * Real.exp (t * value i) / tiltedMoment probability value 0 t
  have hZ := tiltedMoment_zero_positive probability value hp hs t
  have hzero : tiltedMoment probability value 0 t = ∑ i, probability i * Real.exp (t * value i) := by
    simp only [tiltedMoment, pow_zero, mul_one]
  have hw : ∀ i, 0 ≤ weights i := fun i => div_nonneg (mul_nonneg (hp i).le (Real.exp_pos _).le) hZ.le
  have hsum : (∑ i, weights i) = 1 := by
    dsimp only [weights]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    rw [← hzero]
    exact mul_inv_cancel₀ (ne_of_gt hZ)
  have hfirst : (∑ i, weights i * value i) = tiltedMean probability value t := by
    unfold tiltedMean
    dsimp only [weights]
    rw [hzero]
    unfold tiltedMoment
    simp only [div_eq_mul_inv, pow_one]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  have hsecond : (∑ i, weights i * value i ^ 2) =
      tiltedMoment probability value 2 t / tiltedMoment probability value 0 t := by
    unfold tiltedMoment
    dsimp only [weights]
    rw [hzero]
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  have he := bounded_variance_interval weights value hw hsum lower upper hv
  rw [hfirst, hsecond] at he
  exact he

noncomputable def logMoment {n : ℕ} (probability value : Fin n → ℝ) (t : ℝ) : ℝ :=
  Real.log (tiltedMoment probability value 0 t)

theorem logMoment_derivative {n : ℕ} (probability value : Fin n → ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1) (t : ℝ) :
    HasDerivAt (logMoment probability value) (tiltedMean probability value t) t :=
  (tiltedMoment_derivative probability value 0 t).log
    (ne_of_gt (tiltedMoment_zero_positive probability value hp hs t))

theorem finite_hoeffding_logMoment {n : ℕ} (probability value : Fin n → ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (lower upper : ℝ) (hv : ∀ i, lower ≤ value i ∧ value i ≤ upper)
    (t : ℝ) (ht : 0 ≤ t) :
    logMoment probability value t ≤ t * (∑ i, probability i * value i) +
      t ^ 2 * (upper - lower) ^ 2 / 8 := by
  let varianceBound := (upper - lower) ^ 2 / 4
  let mean0 := ∑ i, probability i * value i
  have hmean0 : tiltedMean probability value 0 = mean0 := by
    simp only [tiltedMean, tiltedMoment, zero_mul, Real.exp_zero, mul_one, pow_one, pow_zero, hs, div_one, mean0]
  have hlog0 : logMoment probability value 0 = 0 := by
    simp only [logMoment, tiltedMoment, zero_mul, Real.exp_zero, mul_one, pow_zero, hs, Real.log_one]
  let meanGap := fun s : ℝ => mean0 + varianceBound * s - tiltedMean probability value s
  have hmeanDeriv : ∀ s : ℝ, HasDerivAt meanGap (varianceBound - tiltedVariance probability value s) s := by
    intro s
    have he := ((hasDerivAt_const s mean0).add ((hasDerivAt_id s).const_mul varianceBound)).sub
      (tiltedMean_derivative probability value hp hs s)
    convert he using 1
    · funext s
      rfl
    · simp only [zero_add, mul_one]
  have hmeanMono : MonotoneOn meanGap (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro s _
      exact (hmeanDeriv s).continuousAt.continuousWithinAt
    · intro s _
      exact (hmeanDeriv s).hasDerivWithinAt
    · intro s _
      exact sub_nonneg.mpr (tiltedVariance_bound probability value hp hs lower upper s hv)
  have hmeanBound : ∀ s : ℝ, 0 ≤ s → tiltedMean probability value s ≤ mean0 + varianceBound * s := by
    intro s hs0
    have he := hmeanMono (by simp) hs0 hs0
    have hzero : meanGap 0 = 0 := by dsimp [meanGap]; rw [hmean0]; ring
    rw [hzero] at he
    dsimp [meanGap] at he
    linarith
  let logGap := fun s : ℝ => mean0 * s + varianceBound * s ^ 2 / 2 - logMoment probability value s
  have hlogDeriv : ∀ s : ℝ,
      HasDerivAt logGap (mean0 + varianceBound * s - tiltedMean probability value s) s := by
    intro s
    have he := (((hasDerivAt_id s).const_mul mean0).add
      (((hasDerivAt_id s).pow 2).const_mul (varianceBound / 2))).sub
        (logMoment_derivative probability value hp hs s)
    convert he using 1
    · funext s
      dsimp [logGap]
      ring_nf
    · simp
      ring_nf
  have hlogMono : MonotoneOn logGap (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro s _
      exact (hlogDeriv s).continuousAt.continuousWithinAt
    · intro s _
      exact (hlogDeriv s).hasDerivWithinAt
    · intro s hs0
      have he := hmeanBound s (interior_subset hs0)
      linarith
  have he := hlogMono (by simp) ht ht
  have hzero : logGap 0 = 0 := by dsimp [logGap]; rw [hlog0]; ring
  rw [hzero] at he
  dsimp [logGap, varianceBound, mean0] at he
  nlinarith

theorem log_normalizer_signed_sharp {n : ℕ} (probability loss : Fin n → ℝ)
    (eta cap : ℝ) (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (heta : 0 ≤ eta) (hl : ∀ i, |loss i| ≤ cap) :
    Real.log (normalizer probability loss eta) ≤
      -eta * (∑ i, probability i * loss i) + eta ^ 2 * cap ^ 2 / 2 := by
  have hv : ∀ i, -cap ≤ -loss i ∧ -loss i ≤ cap := by
    intro i
    have he := abs_le.mp (hl i)
    constructor <;> linarith
  have he := finite_hoeffding_logMoment probability (fun i => -loss i) hp hs (-cap) cap hv eta heta
  have hZ : logMoment probability (fun i => -loss i) eta = Real.log (normalizer probability loss eta) := by
    unfold logMoment tiltedMoment normalizer
    simp only [pow_zero, mul_one, mul_neg, neg_mul]
  have hmean : (∑ i, probability i * -loss i) = -(∑ i, probability i * loss i) := by
    simp only [mul_neg, Finset.sum_neg_distrib]
  rw [hZ, hmean] at he
  nlinarith

theorem relativeEntropy_step_signed_sharp {n : ℕ} (comparator probability loss : Fin n → ℝ)
    (eta cap : ℝ) (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (hu : ∑ i, comparator i = 1) (heta : 0 ≤ eta) (hl : ∀ i, |loss i| ≤ cap) :
    eta * (∑ i, (probability i - comparator i) * loss i) ≤
      relativeEntropy comparator probability - relativeEntropy comparator (normalizedUpdate probability loss eta) +
        eta ^ 2 * cap ^ 2 / 2 := by
  have he := relativeEntropy_step_identity comparator probability loss eta hp hs hu
  have hb := log_normalizer_signed_sharp probability loss eta cap hp hs heta hl
  have hsum : (∑ i, (probability i - comparator i) * loss i) =
      (∑ i, probability i * loss i) - ∑ i, comparator i * loss i := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  linarith

theorem finite_signed_sharp_regret {n : ℕ} (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ) (cap : ℕ → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (heta : 0 ≤ eta) (hl : ∀ t i, |loss t i| ≤ cap t)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      relativeEntropy comparator (probability 0) +
        (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, cap t ^ 2) := by
  have htelescope : ∀ T,
      eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
        relativeEntropy comparator (probability 0) - relativeEntropy comparator (probability T) +
          (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, cap t ^ 2) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have he := relativeEntropy_step_signed_sharp comparator (probability T) (loss T) eta (cap T)
        (hp T) (hs T) hsu heta (hl T)
      rw [← hstep T] at he
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith
  have he := htelescope T
  have hn := relativeEntropy_nonnegative comparator (probability T) hu hsu (hp T) (hs T)
  linarith

theorem finite_uniform_signed_sharp_regret {n : ℕ} (hn : 0 < n) (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ) (cap : ℕ → ℝ)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (hstart : probability 0 = fun _ => 1 / (n : ℝ))
    (heta : 0 ≤ eta) (hl : ∀ t i, |loss t i| ≤ cap t)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      Real.log n + (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, cap t ^ 2) := by
  have he := finite_signed_sharp_regret comparator probability loss eta cap hu hsu hp hs heta hl hstep T
  rw [hstart] at he
  have hb := relativeEntropy_uniform_bound hn comparator hu hsu
  linarith

end SparseMW
end Blotto
