import Blotto.GeneralPaperUniformFieldRelabel

/-! All coefficients of the circle lifting theorem are the actual retained
first weights and the actual native reduced value array. Neither a reduced
value formula nor a field permutation is supplied by the caller. -/
namespace Blotto.GeneralPaperNativeCircleCoefficients
open GeneralPaperNativeReductionShape GeneralPaperFieldRelabel GeneralPaperLightFieldIndexEquiv
open GeneralPaperLightFieldOrder
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem original {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let e := originalEquiv bits model W k input
    let vFirst := (firstSelector bits model W k input v hv).values
    let vReduced := (GeneralPaperOriginalValueReduction.selector bits model W k input v hv).values
    ∃ hm:o.m=o.classified.heavy.size+o.representatives,
      (∀ j:Fin o.classified.heavy.size,
        (values e vFirst).weight (Fin.castAdd o.classified.light.size j)=
          (values (finCongr hm.symm) vReduced).weight (Fin.castAdd o.representatives j)) ∧
      (∀ j:Fin o.classified.light.size,
        (values e vFirst).weight (Fin.natAdd o.classified.heavy.size j)=
          (GeneralPaperCircleActualWeights.weights o j:ℝ)/o.denominator) ∧
      (∀ a:Fin o.representatives,
        (values (finCongr hm.symm) vReduced).weight (Fin.natAdd o.classified.heavy.size a)=
          ((o.classified.lightWeight:ℝ)/o.denominator)/o.representatives) := by
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  obtain ⟨hm,hRow⟩ := original_shape bits model W k input hReplace
  dsimp only
  refine ⟨hm,?_,?_,?_⟩
  · intro j
    have hc := hRow (Fin.castAdd o.representatives j)
    simp only [o,Fin.addCases_left] at hc
    change (((o.firstWeights.read (mapping o.classified (Fin.castAdd o.classified.light.size j)):ℚ)/o.denominator:ℚ):ℝ)=
      (o.values.read (Fin.cast hm.symm (Fin.castAdd o.representatives j)):ℝ)
    rw [heavy_read,hc]
  · intro j
    change (((o.firstWeights.read (mapping o.classified (Fin.natAdd o.classified.heavy.size j)):ℚ)/o.denominator:ℚ):ℝ)=
      (o.firstWeights.read (index o.classified.light j):ℝ)/o.denominator
    rw [light_read]
    simp only [Rat.cast_div,Rat.cast_natCast]
  · intro a
    have hc := hRow (Fin.natAdd o.classified.heavy.size a)
    simp only [o,Fin.addCases_right] at hc
    change (o.values.read (Fin.cast hm.symm (Fin.natAdd o.classified.heavy.size a)):ℝ)=_
    rw [hc]
    simp only [Rat.cast_div,Rat.cast_natCast,Nat.cast_mul,Rat.cast_mul]
    ring

end Blotto.GeneralPaperNativeCircleCoefficients
