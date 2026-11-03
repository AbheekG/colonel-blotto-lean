import Blotto.GeneralPaperEqualPreparationProfileRates
import Blotto.GeneralPaperUniformResourceAlgebra

/-! A single constant, chosen uniformly for the arithmetic model, replaces
per-input evaluation of a storage/cost profile. The resulting reference is
just that constant times a public logarithmic input measure. -/
namespace Blotto.GeneralPaperUniformLinearReference
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem larger_capacity (P : ℕ → ℕ) (hScale : GeneralPaperReferenceScaling.Scale P)
    (W : ℕ) (hW : GeneralPaperReferenceCapacity.referenceWord (P 1) ≤ W) : P W < 2 ^ W := by
  have h := GeneralPaperReferenceCapacity.padded_profile_capacity P hScale
    (W - GeneralPaperReferenceCapacity.referenceWord (P 1))
  simpa only [Nat.add_sub_of_le hW] using h

/-- The witness is one global constant, not a per-instance oracle. -/
theorem uniform_capacity {α : Type*} (P : ℕ → α → ℕ) (L : α → ℕ)
    (hScale : ∀ x, GeneralPaperReferenceScaling.Scale (fun w => P w x))
    (hSmall : Small (P 1) L) : ∃ K : ℕ, 1 ≤ K ∧ ∀ x, P (K * L x) x < 2 ^ (K * L x) := by
  obtain ⟨C, hC⟩ := hSmall
  refine ⟨4 * C + 1, by omega, ?_⟩
  intro x
  apply larger_capacity (fun w => P w x) (hScale x) ((4 * C + 1) * L x)
  unfold GeneralPaperReferenceCapacity.referenceWord
  have h := hC x
  nlinarith only [h]

@[fun_prop]
theorem rational_small {α : Type*} (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) (f L : α → ℕ)
    (hL : ∀ x, 1 ≤ L x) (hf : Small f L) : Small (fun x => model.rat (f x)) L := by
  obtain ⟨C, d, hg⟩ := hFast
  exact primitive_small hg f L hL hf

@[fun_prop]
theorem overhead_small {α : Type*} (n A L : α → ℕ) (_hL : ∀ x, 1 ≤ L x)
    (hn : Small n L) (hA : Small A L) :
    Small (fun x => PaperIndexedArrayConstruction.overhead id (A x) (n x) (n x)) L := by
  have hMajor : Small (fun x => (n x + 1) * (6 * A x + 10 * binaryWordWidth (n x + 1) + 28)) L := by fun_prop
  apply small_mono hMajor
  intro x
  simpa only [Nat.mul_one] using PaperIndexedArrayConstruction.overhead_bound id 1
    (fun w => by change w ≤ 1 * w; omega) (A x) (n x) (n x) le_rfl

end Blotto.GeneralPaperUniformLinearReference
