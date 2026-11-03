import Blotto.GeneralPaperOriginalHeadlineParameters

/-! Sharp branch rates transfer to one shared original-input scale. Only
uniform constants and logarithmic factors change; epsilon powers remain. -/
namespace Blotto.GeneralPaperOriginalHeadlineTransfers
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem native_time (p : Input) (h : p.budget < 1) :
    GeneralPaperNativeSourceTimeHeadline.timeScale (unequalInput p h) ≤ 4 * timeScale p := by
  have hi : ((GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 : ℕ) : ℚ) ≤
      4 * (inputSize p : ℚ) := by exact_mod_cast native_ledger p h
  have he := epsilon_positive p
  have hn := nstar_nonnegative p
  have ht : 0 ≤ nStar p ^ 3 / epsilon p ^ 6 := by positivity
  change ((GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 : ℕ) : ℚ) +
    nStar p ^ 3 / epsilon p ^ 6 ≤ 4 * ((inputSize p : ℚ) + nStar p ^ 3 / epsilon p ^ 6)
  linarith only [hi, ht]

theorem native_space (p : Input) (h : p.budget < 1) :
    GeneralPaperNativeWorkingSpaceHeadline.spaceScale (unequalInput p h) ≤ 4 * spaceScale p := by
  have hi : ((GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 : ℕ) : ℚ) ≤
      4 * (inputSize p : ℚ) := by exact_mod_cast native_ledger p h
  have he := epsilon_positive p
  have hn := nstar_nonnegative p
  have ht : 0 ≤ nStar p ^ 3 / epsilon p ^ 4 := by positivity
  change ((GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 : ℕ) : ℚ) +
    nStar p ^ 3 / epsilon p ^ 4 ≤ 4 * ((inputSize p : ℚ) + nStar p ^ 3 / epsilon p ^ 4)
  linarith only [hi, ht]

theorem native_description (p : Input) (h : p.budget < 1) :
    GeneralPaperNativeReturnedDescriptionHeadline.descriptionScale (unequalInput p h) ≤ 4 * descriptionScale p := by
  have hi : ((GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 : ℕ) : ℚ) ≤
      4 * (inputSize p : ℚ) := by exact_mod_cast native_ledger p h
  have he := epsilon_positive p
  have ht : 0 ≤ nStar p ^ 2 / epsilon p ^ 3 := by positivity
  change ((GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 : ℕ) : ℚ) +
    ((p.n : ℚ) + nStar p ^ 2 / epsilon p ^ 3) ≤ 4 * ((inputSize p : ℚ) + p.n + nStar p ^ 2 / epsilon p ^ 3)
  nlinarith only [hi, ht, Nat.cast_nonneg (α := ℚ) p.n]

theorem original_roundtrip (p : Input) (h : p.budget < 1) :
    GeneralPaperMeasuredReferenceGrowth.original (unequalInput p h) = p := by cases p; rfl

theorem time_positive (p : Input) : (1 : ℚ) ≤ timeScale p := by
  have hi : (1 : ℚ) ≤ inputSize p := by exact_mod_cast input_positive p
  exact hi.trans (time_ge_input p)

theorem raise (p : Input) (R : ℚ) (hR : 0 ≤ R) (cost C D e f : ℕ) (hC : C ≤ D) (he : e ≤ f)
    (h : (cost : ℚ) ≤ (C : ℚ) * R * (logarithm p : ℚ) ^ e) :
    (cost : ℚ) ≤ (D : ℚ) * R * (logarithm p : ℚ) ^ f := by
  have hp : (logarithm p : ℚ) ^ e ≤ (logarithm p : ℚ) ^ f := by
    exact_mod_cast Nat.pow_le_pow_right (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (log_positive p)) he
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hC) hR) hp (by positivity) (by positivity))

theorem native_time_bound (p : Input) (hBudget : p.budget < 1) (cost A e : ℕ)
    (h : (cost : ℚ) ≤ (A : ℚ) * GeneralPaperNativeSourceTimeHeadline.timeScale (unequalInput p hBudget) *
      (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ^ e) :
    (cost : ℚ) ≤ ((A * 4 * 2 ^ e : ℕ) : ℚ) * timeScale p * (logarithm p : ℚ) ^ e := by
  have hR := native_time p hBudget
  have hL : (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ≤
      2 * (logarithm p : ℚ) := by exact_mod_cast native_log p hBudget
  have hp : (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ^ e ≤
      (2 * (logarithm p : ℚ)) ^ e := by gcongr
  have ht : 0 ≤ timeScale p := (by norm_num : (0 : ℚ) ≤ 1).trans (time_positive p)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg A)) hp (by positivity) (by positivity)
  exact (h.trans hm).trans_eq (by push_cast; rw [mul_pow]; ring)

theorem native_scaled_bound (p : Input) (hBudget : p.budget < 1) (R S : ℚ) (hR : 0 ≤ R) (hS : S ≤ 4 * R)
    (cost A e : ℕ) (h : (cost : ℚ) ≤ (A : ℚ) * S *
      (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ^ e) :
    (cost : ℚ) ≤ ((A * 4 * 2 ^ e : ℕ) : ℚ) * R * (logarithm p : ℚ) ^ e := by
  have hL : (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ≤
      2 * (logarithm p : ℚ) := by exact_mod_cast native_log p hBudget
  have hp : (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ^ e ≤
      (2 * (logarithm p : ℚ)) ^ e := by gcongr
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg A)) hp (by positivity) (by positivity)
  exact (h.trans hm).trans_eq (by push_cast; rw [mul_pow]; ring)

theorem native_space_bound (p : Input) (hBudget : p.budget < 1) (cost A e : ℕ)
    (h : (cost : ℚ) ≤ (A : ℚ) * GeneralPaperNativeWorkingSpaceHeadline.spaceScale (unequalInput p hBudget) *
      (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ^ e) :
    (cost : ℚ) ≤ ((A * 4 * 2 ^ e : ℕ) : ℚ) * spaceScale p * (logarithm p : ℚ) ^ e :=
  native_scaled_bound p hBudget (spaceScale p) _
    ((Nat.cast_nonneg (inputSize p)).trans (space_ge_input p)) (native_space p hBudget) cost A e h

theorem native_description_bound (p : Input) (hBudget : p.budget < 1) (cost A e : ℕ)
    (h : (cost : ℚ) ≤ (A : ℚ) * GeneralPaperNativeReturnedDescriptionHeadline.descriptionScale (unequalInput p hBudget) *
      (GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p hBudget) : ℚ) ^ e) :
    (cost : ℚ) ≤ ((A * 4 * 2 ^ e : ℕ) : ℚ) * descriptionScale p * (logarithm p : ℚ) ^ e :=
  native_scaled_bound p hBudget (descriptionScale p) _
    ((Nat.cast_nonneg (inputSize p)).trans (description_ge_input p)) (native_description p hBudget) cost A e h

theorem equal_scaled_bound (model : RationalCostModel) (p : Input) (R : ℚ) (hR : (inputSize p : ℚ) ≤ R)
    (cost A e : ℕ) (h : cost ≤ A * GeneralPaperEqualInputHeadline.inputSize (equalInput model p) *
      GeneralPaperEqualInputHeadline.paperLog (equalInput model p) ^ e) :
    (cost : ℚ) ≤ (A : ℚ) * R * (logarithm p : ℚ) ^ e := by
  have hQ : (cost : ℚ) ≤ (A : ℚ) * (inputSize p : ℚ) *
      (GeneralPaperEqualInputHeadline.paperLog (equalInput model p) : ℚ) ^ e := by exact_mod_cast h
  have hp : (GeneralPaperEqualInputHeadline.paperLog (equalInput model p) : ℚ) ^ e ≤
      (logarithm p : ℚ) ^ e := by exact_mod_cast Nat.pow_le_pow_left (equal_log model p) e
  have hPositive : 0 ≤ R := (Nat.cast_nonneg (inputSize p)).trans hR
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg A)) hp (by positivity) (by positivity)
  exact hQ.trans hm

end Blotto.GeneralPaperOriginalHeadlineTransfers
