import Blotto.GeneralPaperUniformLawMap

/-! The erased law of the actual native original-field evaluator chooses
one uniform whole row and one independent uniform shift. It equals the
selected original law, including shared budget scaling and all row ties.
The native fair-bit implementation of these choices remains separate. -/
namespace Blotto.GeneralPaperOriginalDrawLaw
open GeneralPaperOriginalCirclePreparation GeneralPaperLightFieldIndexEquiv
set_option autoImplicit false
set_option maxHeartbeats 2800000

noncomputable def law {n T S : ℕ} (hT : 0<T) (hS : 0<S) (model : RationalCostModel)
    (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) : Mixed n :=
  GeneralPaperUniformRowLaw.mixture hT (fun i => GeneralPaperUniformRowLaw.law hS
    (fun l => (fun j => ((draw model o hR c prepared i l).1.read j:ℝ))))

theorem data {n T K S : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T)
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (hS : 0<S) (c : ℚ)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o) (hBijective : Function.Bijective (mapping o.classified)) :
    law hT hS model o hR c (run price index A o hm columns).1=
      scaleLaw (c:ℝ) (GeneralPaperFieldRelabel.law (Equiv.ofBijective (mapping o.classified) hBijective).symm
        (GeneralPaperSelectedCircleLaw.law o.representatives o.classified.lightWeight S hR hW hS hT
          (GeneralPaperCircleActualWeights.weights o) (fun r => GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
            ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow r)))) := by
  unfold law GeneralPaperSelectedCircleLaw.law
  rw [GeneralPaperUniformLawMap.relabel_mixture,GeneralPaperUniformLawMap.scale_mixture]
  congr 1
  funext i
  rw [GeneralPaperUniformFieldRelabel.uniform,GeneralPaperDictionaryUniformLaw.scaled_uniform]
  congr 1
  funext l
  exact GeneralPaperOriginalCirclePointwise.data price index A model o hm columns hT hR hW hS c hConserved hBijective i l

theorem original {n T K S : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (columns : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model W k input).1.m (GeneralPaperQuantizedColumn.Column T K))
    (hT : 0<T) (hS : 0<S) (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    law hT hS model o (GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input) c
      (run price index A o hm columns).1=
      scaleLaw (c:ℝ) (GeneralPaperNativeSelectedSecurity.lifted bits model W k input v hv hReplace hm S hS hT
        (GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow) :=
  data price index A model _ hm columns hT
    (GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input)
    (GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv
      (GeneralPaperNativeCircleLoss.original_light_positive bits model W k input hReplace)) hS c
    (GeneralPaperCircleActualWeights.original_sum bits model W k input) (original_bijective bits model W k input)

end Blotto.GeneralPaperOriginalDrawLaw
