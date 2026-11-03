import Blotto.GeneralPaperMixedCircleLift
import Blotto.GeneralPaperNativeCircleSecurity

/-! Arbitrary-law full-cell reconstruction on the actual named original
battlefields, with the paper's 9e/40 loss. The continuous-rotation geometric
identification remains separate from this all-whole-laws security theorem. -/
namespace Blotto.GeneralPaperNativeMixedCircleSecurity
open GeneralPaperNativeReductionShape GeneralPaperNativeCircleLoss
open GeneralPaperFieldRelabel GeneralPaperLightFieldIndexEquiv
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

noncomputable def lifted {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, input.read j = v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced = true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m =
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size +
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (P : Mixed (GeneralPaperOriginalValueReduction.run bits model W k input).1.m) : Mixed n :=
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let hR := original_representatives_positive bits model W k input
  let hG := original_light_positive bits model W k input hReplace
  let hL := GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv hG
  law (originalEquiv bits model W k input).symm
    (GeneralPaperMixedCircleLift.law o.representatives o.classified.lightWeight hR hL
      (GeneralPaperCircleActualWeights.weights o) (law (finCongr hm.symm) P))

theorem original {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, input.read j = v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced = true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let vFirst := (firstSelector bits model W k input v hv).values
    let vReduced := (GeneralPaperOriginalValueReduction.selector bits model W k input v hv).values
    ∃ hm : o.m = o.classified.heavy.size + o.representatives,
      ∀ (P : Mixed o.m) (B : ℝ), 0 ≤ B →
        security vFirst B (lifted bits model W k input v hv hReplace hm P) ≤
          security vReduced B P + 9*(1/(2 : ℝ)^k)/40 := by
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  obtain ⟨hm, hK, hLight, hRep⟩ := GeneralPaperNativeCircleCoefficients.original bits model W k input v hv hReplace
  dsimp only
  refine ⟨hm, ?_⟩
  intro P B hB
  let e := originalEquiv bits model W k input
  let vFirst := (firstSelector bits model W k input v hv).values
  let vReduced := (GeneralPaperOriginalValueReduction.selector bits model W k input v hv).values
  let hR := original_representatives_positive bits model W k input
  let hG := original_light_positive bits model W k input hReplace
  let hL := GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv hG
  have hBound := GeneralPaperMixedCircleLift.security_bound o.representatives o.classified.lightWeight o.denominator
    hR hL (original_first_valid bits model W k input v hv).1
    (GeneralPaperCircleActualWeights.weights o) (GeneralPaperCircleActualWeights.original_positive bits model W k input v hv)
    (GeneralPaperCircleActualWeights.original_sum bits model W k input)
    (values e vFirst) (values (finCongr hm.symm) vReduced) hK hLight hRep
    (law (finCongr hm.symm) P) B hB
  have hRestore := restored_security e vFirst B
    (GeneralPaperMixedCircleLift.law o.representatives o.classified.lightWeight hR hL
      (GeneralPaperCircleActualWeights.weights o) (law (finCongr hm.symm) P))
  have hReduced := security_relabel (finCongr hm.symm) vReduced B P
  have hError := combined_bound bits model W k input v hv hReplace
  change security vFirst B (law e.symm
    (GeneralPaperMixedCircleLift.law o.representatives o.classified.lightWeight hR hL
      (GeneralPaperCircleActualWeights.weights o) (law (finCongr hm.symm) P))) ≤ _
  rw [hRestore]
  rw [hReduced] at hBound
  exact hBound.trans (by linarith only [hError])

theorem supported {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, input.read j = v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced = true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m =
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size +
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (P : Mixed (GeneralPaperOriginalValueReduction.run bits model W k input).1.m)
    (B : ℝ) (hP : Supported B P) :
    Supported B (lifted bits model W k input v hv hReplace hm P) := by
  apply GeneralPaperFieldRelabel.supported
  apply GeneralPaperMixedCircleLift.supported
  · exact GeneralPaperCircleActualWeights.original_sum bits model W k input
  · exact GeneralPaperFieldRelabel.supported _ P B hP

end Blotto.GeneralPaperNativeMixedCircleSecurity
