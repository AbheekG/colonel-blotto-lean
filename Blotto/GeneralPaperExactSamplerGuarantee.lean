import Blotto.GeneralPaperExactSamplerNativeHeadlines

/-! Canonical continuous regrets and hard budgets of the refined sampler.
The whole allocation laws agree with the checked retained reference laws;
every shorter direct bit path is feasible, including at zero ties. -/
namespace Blotto.GeneralPaperExactSamplerGuarantee
open GeneralPaperStoredStrategySampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def Guarantee {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (v : Values n) (b epsilon : ℝ) (sampler : Sampler n T K) : Prop :=
  let μ := GeneralPaperExactStoredSampler.law bits primitive A model sampler false
  let ν := GeneralPaperExactStoredSampler.law bits primitive A model sampler true
  Supported 1 μ ∧ Supported b ν ∧ regret v 1 μ ν ≤ epsilon ∧ regret v b ν μ ≤ epsilon ∧
    ∀ fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool,
      Feasible 1 (fun j => ((GeneralPaperExactStoredSampler.run bits primitive A model sampler false fresh).output.read j : ℝ)) ∧
      Feasible b (fun j => ((GeneralPaperExactStoredSampler.run bits primitive A model sampler true fresh).output.read j : ℝ))

theorem of_reference {n T K : ℕ} {bits : Bool} {primitive : ℕ → ℕ} {A : ℕ} {model : RationalCostModel}
    {v : Values n} {b epsilon : ℝ} {sampler : Sampler n T K}
    (h : GeneralPaperClosedStrategyEquilibrium.Guarantee bits primitive A model v b epsilon sampler) :
    Guarantee bits primitive A model v b epsilon sampler := by
  dsimp only [Guarantee]
  simp only [GeneralPaperExactStoredSampler.old_law]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun fresh =>
    ⟨GeneralPaperExactStoredSampler.every_output_feasible bits primitive A model sampler false 1 h.1 fresh,
     GeneralPaperExactStoredSampler.every_output_feasible bits primitive A model sampler true b h.2.1 fresh⟩⟩

end Blotto.GeneralPaperExactSamplerGuarantee
