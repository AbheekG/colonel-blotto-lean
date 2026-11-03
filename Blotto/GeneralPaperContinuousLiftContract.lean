import Blotto.GeneralPaperContinuousCircleLaw

/-! The continuous-rotation security statement of lem:general:lift for
every reduced whole-law, with the exact squared-value loss and native
9e/40 specialization. Positive-overlap minima identify the actual law. -/
namespace Blotto.GeneralPaperContinuousLiftContract
open GeneralPaperFieldRelabel GeneralPaperLightFieldIndexEquiv
open GeneralPaperNativeReductionShape GeneralPaperNativeCircleLoss
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem security_bound {h g : ℕ} (R W Q : ℕ) (hR : 0 < R) (hW : 0 < W) (hQ : 0 < Q)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (hs : ∑ j, weights j = W)
    (v : Values (h+g)) (vRed : Values (h+R))
    (hk : ∀ j : Fin h, v.weight (Fin.castAdd g j) = vRed.weight (Fin.castAdd R j))
    (hl : ∀ j : Fin g, v.weight (Fin.natAdd h j) = (weights j : ℝ)/Q)
    (hr : ∀ a : Fin R, vRed.weight (Fin.natAdd h a) = ((W : ℝ)/Q)/R)
    (P : Mixed (h+R)) (B : ℝ) (hB : 0 ≤ B) :
    security v B (GeneralPaperContinuousCircleLaw.law R W weights P) ≤ security vRed B P +
      (∑ j, ((weights j : ℝ)/Q)^2)/((W : ℝ)/Q) + ((W : ℝ)/Q)/R := by
  rw [GeneralPaperContinuousCircleLaw.law_eq R W hR hW weights hp P,
    ← GeneralPaperCircleLightPayoff.normalized_weight_loss W Q hW hQ weights]
  exact GeneralPaperMixedCircleLift.security_bound R W Q hR hW hQ weights hp hs v vRed hk hl hr P B hB

noncomputable def lifted {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (_hv : ∀ j, input.read j = v.weight j)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m =
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size +
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (P : Mixed (GeneralPaperOriginalValueReduction.run bits model W k input).1.m) : Mixed n :=
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  law (originalEquiv bits model W k input).symm
    (GeneralPaperContinuousCircleLaw.law o.representatives o.classified.lightWeight
      (GeneralPaperCircleActualWeights.weights o) (law (finCongr hm.symm) P))

theorem lifted_eq {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, input.read j = v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced = true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m =
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size +
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (P : Mixed (GeneralPaperOriginalValueReduction.run bits model W k input).1.m) :
    lifted bits model W k input v hv hm P =
      GeneralPaperNativeMixedCircleSecurity.lifted bits model W k input v hv hReplace hm P := by
  let hG := original_light_positive bits model W k input hReplace
  let hL := GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv hG
  apply congrArg (law (originalEquiv bits model W k input).symm)
  exact GeneralPaperContinuousCircleLaw.law_eq _ _ (original_representatives_positive bits model W k input) hL
    (GeneralPaperCircleActualWeights.weights _) (GeneralPaperCircleActualWeights.original_positive bits model W k input v hv)
    (law (finCongr hm.symm) P)

theorem paper_lift {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, input.read j = v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced = true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let vFirst := (firstSelector bits model W k input v hv).values
    let vReduced := (GeneralPaperOriginalValueReduction.selector bits model W k input v hv).values
    ∃ hm : o.m = o.classified.heavy.size + o.representatives,
      ∀ P : Mixed o.m,
        (Supported 1 P → Supported 1 (lifted bits model W k input v hv hm P)) ∧
        ∀ B : ℝ, 0 ≤ B → security vFirst B (lifted bits model W k input v hv hm P) ≤
          security vReduced B P + 9*(1/(2 : ℝ)^k)/40 := by
  obtain ⟨hm, hBound⟩ := GeneralPaperNativeMixedCircleSecurity.original bits model W k input v hv hReplace
  refine ⟨hm, fun P => ?_⟩
  rw [lifted_eq bits model W k input v hv hReplace hm P]
  exact ⟨fun hP => GeneralPaperNativeMixedCircleSecurity.supported bits model W k input v hv hReplace hm P 1 hP,
    fun B hB => hBound P B hB⟩

end Blotto.GeneralPaperContinuousLiftContract
