import Blotto.SizedImplicitSampler

/-! An exact native implementation of a sized stored sampler transfers its
already proved budget and target law. Concrete direct-access constructors must
derive refinement; this interface alone is not a claimed sampler implementation. -/

namespace Blotto.ImplicitLeafCounts

structure ExactSizedDraw (m : ℕ) where
  model : SizedImplicitSampler m
  draw : (epsilon : ℚ) → (Fin (model.bitBudget epsilon) → Bool) → Fin m → ℚ
  refines : ∀ epsilon bits, draw epsilon bits = model.sample epsilon bits

namespace ExactSizedDraw

def bitBudget {m : ℕ} (prepared : ExactSizedDraw m) (epsilon : ℚ) : ℕ := prepared.model.bitBudget epsilon
def budget {m : ℕ} (prepared : ExactSizedDraw m) : ℚ := prepared.model.budget

theorem draw_feasible {m : ℕ} (prepared : ExactSizedDraw m) (epsilon : ℚ) (he : 0 < epsilon)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) :
    Feasible (prepared.budget : ℝ) (fun field => (prepared.draw epsilon bits field : ℝ)) := by
  change Fin (prepared.model.bitBudget epsilon) → Bool at bits
  change Feasible (prepared.model.budget : ℝ) (fun field => (prepared.draw epsilon bits field : ℝ))
  rw [prepared.refines]
  exact prepared.model.sample_feasible epsilon he bits

noncomputable def nativeKernel {m : ℕ} (prepared : ExactSizedDraw m) (epsilon : ℚ) :
    BoundedExpectationKernel (Fin m → ℚ) := (fairBitKernel (prepared.bitBudget epsilon)).map (prepared.draw epsilon)

theorem nativeKernel_mean_eq {m : ℕ} (prepared : ExactSizedDraw m) (epsilon : ℚ) (test : (Fin m → ℚ) → ℝ) :
    (prepared.nativeKernel epsilon).mean test = (prepared.model.nativeKernel epsilon).mean test := by
  change (fairBitKernel (prepared.model.bitBudget epsilon)).mean (fun bits => test (prepared.draw epsilon bits)) = _
  have he : (fun bits => test (prepared.draw epsilon bits)) = fun bits => test (prepared.model.sample epsilon bits) := by
    funext bits
    rw [prepared.refines]
  rw [he]
  rfl

theorem nativeKernel_close {m : ℕ} (prepared : ExactSizedDraw m) (epsilon : ℚ) (he : 0 < epsilon) :
    (prepared.nativeKernel epsilon).Close prepared.model.targetKernel (epsilon : ℝ) := by
  intro test hTest
  rw [prepared.nativeKernel_mean_eq]
  exact prepared.model.nativeKernel_close epsilon he test hTest

end ExactSizedDraw
end Blotto.ImplicitLeafCounts
