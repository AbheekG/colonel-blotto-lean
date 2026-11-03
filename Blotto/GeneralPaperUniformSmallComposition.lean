import Blotto.GeneralPaperStoredPreparationPhases

/-! A polynomial resource bound in a larger analysis scale still has
logarithmic encoding length when that scale and the linear mass do.
This permits arbitrary preparation coefficients without replacing them
by constants inside the uniform-growth argument. -/
namespace Blotto.GeneralPaperUniformSmallComposition
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2000000

@[fun_prop]
theorem small_power {α : Type*} (f L : α → ℕ) (d : ℕ) (hL : ∀ x,1 ≤ L x) (hf : Small f L) :
    Small (fun x => f x ^ d) L := by
  induction d with
  | zero => simpa only [pow_zero] using small_constant 1 L hL
  | succ d ih => simpa only [pow_succ] using small_mul _ _ L ih hf

theorem bound_small_scale {α : Type*} {f r M L : α → ℕ}
    (hL : ∀ x,1 ≤ L x) (hBound : Bound f r M) (hr : Small r L) (hM : Small M L) : Small f L := by
  obtain ⟨C,d,hC⟩ := hBound
  have hMajor : Small (fun x => C * r x * M x ^ d) L := by fun_prop
  exact small_mono hMajor hC

theorem tight_log_mono {α : Type*} {f L M : α → ℕ} (hf : Tight f L) (hLM : ∀ x,L x ≤ M x) : Tight f M := by
  obtain ⟨C,hC⟩ := hf
  exact ⟨C,fun x => (hC x).trans (Nat.mul_le_mul_left C (hLM x))⟩

theorem small_log_mono {α : Type*} {f L M : α → ℕ} (hf : Small f L) (hLM : ∀ x,L x ≤ M x) : Small f M :=
  tight_log_mono hf hLM

end Blotto.GeneralPaperUniformSmallComposition
