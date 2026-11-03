import Blotto.GeneralPaperNativeFairSampler

/-! The actual finite-bit sampler has exactly the prior uniform whole-row
and independent-shift law. Two consecutive fresh blocks give the product
of the two whole-player laws, preserving within-allocation dependence. -/
namespace Blotto.GeneralPaperNativeFairSamplerLaw
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def law {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) : Mixed n :=
  (fairBitLaw (R+L)).map (fun fresh => fun j =>
    ((GeneralPaperNativeFairSampler.run primitive A R L T S hT hS model o hR c prepared fresh).output.read j:ℝ))

theorem data {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) :
    law primitive A R L T S hT hS model o hR c prepared=
      GeneralPaperOriginalDrawLaw.law (hT ▸ Nat.two_pow_pos R) (hS ▸ Nat.two_pow_pos L) model o hR c prepared := by
  subst T
  subst S
  simp only [law,GeneralPaperNativeFairSampler.data,Fin.cast_refl,GeneralPaperOriginalDrawLaw.law]
  exact GeneralPaperFairRowShiftLaw.indices R L (fun i l j =>
    ((GeneralPaperOriginalCirclePreparation.draw model o hR c prepared i l).1.read j:ℝ))

theorem independent_players {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c d : ℚ)
    (rich poor : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) :
    Measure.map (fun fresh =>
      ((fun j => ((GeneralPaperNativeFairSampler.run primitive A R L T S hT hS model o hR c rich
          (firstBitBlock (R+L) (R+L) fresh)).output.read j:ℝ)),
        (fun j => ((GeneralPaperNativeFairSampler.run primitive A R L T S hT hS model o hR d poor
          (secondBitBlock (R+L) (R+L) fresh)).output.read j:ℝ))))
      (fairBitLaw ((R+L)+(R+L)) : Measure (Fin ((R+L)+(R+L)) → Bool))=
      (law primitive A R L T S hT hS model o hR c rich : Measure (Allocation n)).prod
        (law primitive A R L T S hT hS model o hR d poor : Measure (Allocation n)) := by
  exact fairBitBlocks_map_product (R+L) (R+L)
    (fun fresh j => ((GeneralPaperNativeFairSampler.run primitive A R L T S hT hS model o hR c rich fresh).output.read j:ℝ))
    (fun fresh j => ((GeneralPaperNativeFairSampler.run primitive A R L T S hT hS model o hR d poor fresh).output.read j:ℝ))

end Blotto.GeneralPaperNativeFairSamplerLaw
