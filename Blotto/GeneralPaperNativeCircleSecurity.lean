import Blotto.GeneralPaperNativeCircleLoss

/-! The full finite-cell lifting security theorem now uses the actual
native first weights, reduced values and original named-field maps. Whole
uniform source rows may be arbitrarily correlated within a row. This is
the all-cell mathematical lift; native selected-shift sampling/prices and
the final deterministic driver remain separate. -/
namespace Blotto.GeneralPaperNativeCircleSecurity
open GeneralPaperNativeReductionShape GeneralPaperNativeCircleLoss
open GeneralPaperFieldRelabel GeneralPaperLightFieldIndexEquiv
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

noncomputable def lifted {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (hT : 0<T) (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m) : Mixed n :=
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let hR := original_representatives_positive bits model W k input
  let hG := original_light_positive bits model W k input hReplace
  let hL := GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv hG
  law (originalEquiv bits model W k input).symm
    (GeneralPaperCircleCanonicalLift.law o.representatives o.classified.lightWeight hR hL hT
      (GeneralPaperCircleActualWeights.weights o) (fun r => allocation (finCongr hm.symm) (rows r)))

theorem original {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let vFirst := (firstSelector bits model W k input v hv).values
    let vReduced := (GeneralPaperOriginalValueReduction.selector bits model W k input v hv).values
    ∃ hm:o.m=o.classified.heavy.size+o.representatives,
      ∀ (T : ℕ) (hT : 0<T) (rows : Fin T → Allocation o.m) (B : ℝ),0≤B →
        security vFirst B (lifted bits model W k input v hv hReplace hm hT rows)≤
          security vReduced B (GeneralPaperUniformRowLaw.law hT rows)+9*(1/(2:ℝ)^k)/40 := by
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  obtain ⟨hm,hK,hLight,hRep⟩ := GeneralPaperNativeCircleCoefficients.original bits model W k input v hv hReplace
  dsimp only
  refine ⟨hm,?_⟩
  intro T hT rows B hB
  let e := originalEquiv bits model W k input
  let vFirst := (firstSelector bits model W k input v hv).values
  let vReduced := (GeneralPaperOriginalValueReduction.selector bits model W k input v hv).values
  let hR := original_representatives_positive bits model W k input
  let hG := original_light_positive bits model W k input hReplace
  let hL := GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv hG
  have hBound := GeneralPaperCircleCanonicalLift.security_bound o.representatives o.classified.lightWeight o.denominator
    hR hL (original_first_valid bits model W k input v hv).1 hT
    (GeneralPaperCircleActualWeights.weights o) (GeneralPaperCircleActualWeights.original_positive bits model W k input v hv)
    (GeneralPaperCircleActualWeights.original_sum bits model W k input)
    (values e vFirst) (values (finCongr hm.symm) vReduced) hK hLight hRep
    (fun r => allocation (finCongr hm.symm) (rows r)) B hB
  have hRestore := restored_security e vFirst B
    (GeneralPaperCircleCanonicalLift.law o.representatives o.classified.lightWeight hR hL hT
      (GeneralPaperCircleActualWeights.weights o) (fun r => allocation (finCongr hm.symm) (rows r)))
  have hReduced := GeneralPaperUniformFieldRelabel.security (finCongr hm.symm) hT rows vReduced B
  have hError := combined_bound bits model W k input v hv hReplace
  change security vFirst B (law e.symm
    (GeneralPaperCircleCanonicalLift.law o.representatives o.classified.lightWeight hR hL hT
      (GeneralPaperCircleActualWeights.weights o) (fun r => allocation (finCongr hm.symm) (rows r))))≤_
  rw [hRestore]
  rw [hReduced] at hBound
  exact hBound.trans (by linarith only [hError])

theorem supported {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (hT : 0<T) (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m)
    (B : ℝ) (hRows : ∀ r,Feasible B (rows r)) :
    Supported B (lifted bits model W k input v hv hReplace hm hT rows) := by
  apply GeneralPaperFieldRelabel.supported
  apply GeneralPaperCircleCanonicalLift.law_supported
  · exact GeneralPaperCircleActualWeights.original_sum bits model W k input
  · intro r
    exact (feasible_iff (finCongr hm.symm) B (rows r)).mpr (hRows r)

end Blotto.GeneralPaperNativeCircleSecurity
