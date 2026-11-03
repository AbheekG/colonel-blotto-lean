import Blotto.RationalWeightedProposalLaw

/-! One rational proposal node samples its finite conditional choices with
bounded fair-bit categorical blocks. Zero normalizers return failure; positive
labels are checked before return, so impossible zero-weight paths are rejected. -/

namespace Blotto
open scoped BigOperators

def positiveRationalChoice {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (K : ℕ) (bits : ℕ → Bool) : Option (Fin r) :=
  if hr : 0 < r then
    let fallback : Fin r := ⟨0, hr⟩
    let total := ∑ i, weights i
    if ht : 0 < total then
      let probabilities := fun i => weights i / total
      let a : RationalFiniteAttempt r r := {
        weight := probabilities
        nonnegative := fun i => div_nonneg (hn i) ht.le
        sum_one := by
          simp only [probabilities, div_eq_mul_inv]
          rw [← Finset.sum_mul]
          exact mul_inv_cancel₀ (ne_of_gt ht)
        decode := fun i => if 0 < weights i then some i else none
        fallbackLabel := fallback }
      a.sample K (fun j => bits j.val)
    else none
  else none

theorem positiveRationalChoice_positive {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (K : ℕ) (bits : ℕ → Bool) (i : Fin r) (hi : positiveRationalChoice weights hn K bits = some i) :
    0 < weights i := by
  unfold positiveRationalChoice at hi
  split at hi
  · dsimp only at hi
    split at hi
    · dsimp only [RationalFiniteAttempt.sample] at hi
      split at hi
      · rename_i hSelected
        have he := Option.some.inj hi
        rw [he] at hSelected
        exact hSelected
      · cases hi
    · cases hi
  · cases hi

namespace RationalWeightedFamily

theorem prefixMass_nonnegative {n : ℕ} (a : RationalWeightedFamily n) (B : ℚ) : 0 ≤ a.prefixMass B := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact a.mass_nonnegative i
  · exact le_rfl

def conditionalSample {n : ℕ} (a : RationalWeightedFamily n) (B : ℚ) (K : ℕ) (bits : ℕ → Bool) : Option (Fin n) :=
  positiveRationalChoice (fun i => if a.resource i ≤ B then a.mass i else 0)
    (by intro i; split_ifs; exact a.mass_nonnegative i; exact le_rfl) K bits

theorem conditionalSample_contract {n : ℕ} (a : RationalWeightedFamily n) (B : ℚ) (K : ℕ)
    (bits : ℕ → Bool) (i : Fin n) (hi : a.conditionalSample B K bits = some i) :
    a.resource i ≤ B ∧ 0 < a.mass i := by
  have hp := positiveRationalChoice_positive _ _ K bits i hi
  by_cases hr : a.resource i ≤ B
  · exact ⟨hr, by simpa only [hr, ite_true] using hp⟩
  · simp only [hr, ite_false, lt_self_iff_false] at hp

theorem convolution_prefix_right {n m : ℕ} (a : RationalWeightedFamily n) (b : RationalWeightedFamily m) (B : ℚ) :
    a.convolution b B = ∑ i, a.mass i * b.prefixMass (B - a.resource i) := by
  unfold convolution prefixMass
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : a.resource i + b.resource j ≤ B ↔ b.resource j ≤ B - a.resource i := by constructor <;> intro h <;> linarith
  simp only [he]
  split_ifs <;> simp

theorem selected_convolution_positive {n m : ℕ} (a : RationalWeightedFamily n) (b : RationalWeightedFamily m)
    (B : ℚ) (i : Fin n) (hs : 0 < a.mass i * b.prefixMass (B - a.resource i)) :
    0 < a.convolution b B := by
  rw [convolution_prefix_right]
  exact hs.trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (a.mass_nonnegative j) (b.prefixMass_nonnegative _)) (Finset.mem_univ i))

def syntheticSample {n m : ℕ} (a : RationalWeightedFamily n) (b : RationalWeightedFamily m)
    (B : ℚ) (K : ℕ) (bits : ℕ → Bool) : Option (Fin n) :=
  positiveRationalChoice (fun i => a.mass i * b.prefixMass (B - a.resource i))
    (fun i => mul_nonneg (a.mass_nonnegative i) (b.prefixMass_nonnegative _)) K bits

theorem syntheticSample_positive {n m : ℕ} (a : RationalWeightedFamily n) (b : RationalWeightedFamily m)
    (B : ℚ) (K : ℕ) (bits : ℕ → Bool) (i : Fin n) (hi : a.syntheticSample b B K bits = some i) :
    0 < a.mass i * b.prefixMass (B - a.resource i) :=
  positiveRationalChoice_positive _ _ K bits i hi

end RationalWeightedFamily
end Blotto
