import Blotto.FiniteImportanceRejection

/-! Bounded repeated rejection has one global attempt loop. Exact output and
failure masses are derived recursively; fallback bias is at most failure mass
for every event. No exact rational-coin bit implementation is asserted here. -/

namespace Blotto
open scoped BigOperators Classical

def rejectionFailure (p : ℝ) (k : ℕ) : ℝ := (1 - p) ^ k

def rejectionSuccessMass (p q : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => q + (1 - p) * rejectionSuccessMass p q k

def rejectionExpectedAttempts (p : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => 1 + (1 - p) * rejectionExpectedAttempts p k

theorem rejectionSuccessMass_factor (p q : ℝ) (k : ℕ) :
    rejectionSuccessMass p q k = q * rejectionExpectedAttempts p k := by
  induction k with
  | zero => simp [rejectionSuccessMass, rejectionExpectedAttempts]
  | succ k ih => rw [rejectionSuccessMass, rejectionExpectedAttempts, ih]; ring

theorem rejectionExpectedAttempts_identity (p : ℝ) (k : ℕ) :
    p * rejectionExpectedAttempts p k = 1 - rejectionFailure p k := by
  induction k with
  | zero => simp [rejectionExpectedAttempts, rejectionFailure]
  | succ k ih =>
    unfold rejectionFailure at ih ⊢
    rw [rejectionExpectedAttempts, pow_succ]
    calc
      p * (1 + (1 - p) * rejectionExpectedAttempts p k) =
          p + (1 - p) * (p * rejectionExpectedAttempts p k) := by ring
      _ = p + (1 - p) * (1 - (1 - p) ^ k) := by rw [ih]
      _ = _ := by ring

theorem rejectionFailure_unit {p : ℝ} (hp : 0 ≤ p) (h1 : p ≤ 1) (k : ℕ) :
    0 ≤ rejectionFailure p k ∧ rejectionFailure p k ≤ 1 := by
  unfold rejectionFailure
  exact ⟨pow_nonneg (by linarith) _, pow_le_one₀ (by linarith) (by linarith)⟩

theorem rejectionExpectedAttempts_nonnegative {p : ℝ} (h1 : p ≤ 1) (k : ℕ) :
    0 ≤ rejectionExpectedAttempts p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rejectionExpectedAttempts]
    have he := mul_nonneg (show 0 ≤ 1 - p by linarith) ih
    linarith

theorem rejectionExpectedAttempts_le_inverse {p : ℝ} (hp : 0 < p) (h1 : p ≤ 1) (k : ℕ) :
    rejectionExpectedAttempts p k ≤ 1 / p := by
  have hi := rejectionExpectedAttempts_identity p k
  have hf := (rejectionFailure_unit (le_of_lt hp) h1 k).1
  apply (le_div_iff₀ hp).mpr
  nlinarith

theorem rejectionExpectedAttempts_le_count {p : ℝ} (hp : 0 ≤ p) (h1 : p ≤ 1) (k : ℕ) :
    rejectionExpectedAttempts p k ≤ k := by
  induction k with
  | zero => simp [rejectionExpectedAttempts]
  | succ k ih =>
    rw [rejectionExpectedAttempts, Nat.cast_add, Nat.cast_one]
    have hnonneg := rejectionExpectedAttempts_nonnegative h1 k
    have hm : (1 - p) * rejectionExpectedAttempts p k ≤ rejectionExpectedAttempts p k := by nlinarith
    linarith

theorem rejectionSuccessMass_closed {p : ℝ} (hp : 0 < p) (q : ℝ) (k : ℕ) :
    rejectionSuccessMass p q k = (1 - rejectionFailure p k) * (q / p) := by
  rw [rejectionSuccessMass_factor, ← rejectionExpectedAttempts_identity]
  field_simp

theorem rejectionFailure_mono_probability {p lower : ℝ} (_hl : 0 ≤ lower)
    (hLower : lower ≤ p) (hp : p ≤ 1) (k : ℕ) :
    rejectionFailure p k ≤ rejectionFailure lower k := by
  unfold rejectionFailure
  exact pow_le_pow_left₀ (by linarith) (by linarith) k

theorem rejectionFallback_event_error {failure target fallback : ℝ}
    (hf : 0 ≤ failure) (ht0 : 0 ≤ target) (ht1 : target ≤ 1)
    (hb0 : 0 ≤ fallback) (hb1 : fallback ≤ 1) :
    |((1 - failure) * target + failure * fallback) - target| ≤ failure := by
  rw [abs_le]
  constructor <;> nlinarith

namespace FiniteImportanceProposal

noncomputable def boundedOutputWeight {r n : ℕ} (q : FiniteImportanceProposal r n)
    (bound : ℝ) (k : ℕ) (x : Fin n) : ℝ :=
  rejectionSuccessMass (q.acceptanceMass bound) (q.acceptedOutputWeight bound x) k

theorem boundedOutputWeight_eq {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (hm : 0 < q.targetMass) (k : ℕ) (x : Fin n) :
    q.boundedOutputWeight bound k x =
      (1 - rejectionFailure (q.acceptanceMass bound) k) * (q.targetWeight x / q.targetMass) := by
  unfold boundedOutputWeight
  rw [rejectionSuccessMass_closed (q.acceptanceMass_positive hb hm), q.conditionalOutput_eq hb hm]

theorem boundedFailure_le {r n : ℕ} (q : FiniteImportanceProposal r n) {z factor : ℝ}
    (hz : 0 < z) (hg : 1 ≤ factor) (hLower : z ≤ q.targetMass)
    (hImportance : ∀ p, q.importance p ≤ z * factor) (k : ℕ) :
    rejectionFailure (q.acceptanceMass (z * factor)) k ≤ (1 - 1 / factor) ^ k := by
  have hg0 : 0 < factor := by linarith
  exact rejectionFailure_mono_probability (le_of_lt (one_div_pos.mpr hg0))
    (q.acceptance_lower_bound hz hg0 hLower)
    (q.acceptanceMass_le_one (mul_pos hz hg0) hImportance) k

theorem boundedExpectedAttempts_le_factor {r n : ℕ} (q : FiniteImportanceProposal r n) {z factor : ℝ}
    (hz : 0 < z) (hg : 1 ≤ factor) (hLower : z ≤ q.targetMass)
    (hImportance : ∀ p, q.importance p ≤ z * factor) (k : ℕ) :
    rejectionExpectedAttempts (q.acceptanceMass (z * factor)) k ≤ factor := by
  have hg0 : 0 < factor := by linarith
  have hm : 0 < q.targetMass := hz.trans_le hLower
  have hp := q.acceptanceMass_positive (mul_pos hz hg0) hm
  have hle := q.acceptanceMass_le_one (mul_pos hz hg0) hImportance
  have hInverse := rejectionExpectedAttempts_le_inverse hp hle k
  have hLowerMass := q.acceptance_lower_bound hz hg0 hLower
  have he : 1 / q.acceptanceMass (z * factor) ≤ factor := by
    apply (div_le_iff₀ hp).mpr
    have hProduct : 1 ≤ factor * q.acceptanceMass (z * factor) :=
      by simpa only [mul_comm] using (div_le_iff₀ hg0).mp hLowerMass
    nlinarith
  exact hInverse.trans he

end FiniteImportanceProposal
end Blotto
