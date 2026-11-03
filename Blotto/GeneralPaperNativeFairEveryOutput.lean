import Blotto.GeneralPaperNativeFairCompiledEquilibrium

/-! Every finite fair-bit vector has positive probability. Thus the hard
budget support guarantee for the actual sampler law holds for every native
realized output, including every extreme vector, without a null exception. -/
namespace Blotto.GeneralPaperNativeFairEveryOutput
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem all {n : ℕ} (K : ℕ) (f : (Fin K → Bool) → Allocation n) (B : ℝ)
    (h : Supported B ((fairBitLaw K).map f)) : ∀ fresh,Feasible B (f fresh) := by
  change ∀ᵐ x ∂Measure.map f (fairBitLaw K : Measure (Fin K → Bool)),Feasible B x at h
  have ha := (ae_map_iff (measurable_of_countable f).aemeasurable (measurable_feasible B)).mp h
  intro fresh
  apply (ae_iff_of_countable.mp ha) fresh
  rw [fairBitLaw_singleton_realWeight]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

theorem native {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) (B : ℝ)
    (h : Supported B (GeneralPaperNativeFairSamplerLaw.law primitive A R L T S hT hS model o hR c prepared)) :
    ∀ fresh,Feasible B (fun j =>
      ((GeneralPaperNativeFairSampler.run primitive A R L T S hT hS model o hR c prepared fresh).output.read j:ℝ)) := by
  exact all (R+L) _ B h

theorem height {n K : ℕ} (price index primitive : ℕ → ℕ) (A Ab R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) (hR : 0<o.representatives) (c : ℚ)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (C H : ℕ) (hc : RationalHeight c C) (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (fresh : Fin (R+L) → Bool) (j : Fin n) :
    RationalHeight ((GeneralPaperNativeFairSampler.run primitive Ab R L T S hT hS model o hR c
      (GeneralPaperOriginalCirclePreparation.run price index A o hm columns).1 fresh).output.read j)
      (C+(binaryWordWidth o.representatives+2*binaryWordWidth o.classified.lightWeight+H)) := by
  rw [GeneralPaperNativeFairSampler.data]
  exact GeneralPaperOriginalDrawBounds.height price index A model o hm columns hR c hConserved hBijective C H hc hColumns _ _ j

end Blotto.GeneralPaperNativeFairEveryOutput
