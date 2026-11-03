import Blotto.GeneralPaperNativeCircleCoefficients

/-! The actual retained native mass and representative count supply the
paper's 9e/40 reconstruction allowance. These are erased bounds on the
existing return, without extra numerical certificate passes. -/
namespace Blotto.GeneralPaperNativeCircleLoss
open GeneralPaperReducedValuesDriver GeneralPaperNativeReductionShape
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def ReplacedCount {n : ℕ} (o : Output n) : Prop := o.replaced=true → o.representatives<o.classified.light.size

theorem reduced_replaced_count {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    ReplacedCount (run bits model W k Q weights).1 := by
  rw [data]
  unfold specification
  split_ifs with he
  · intro _
    exact he
  · intro h
    cases h

theorem original_replaced_count {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ) :
    ReplacedCount (GeneralPaperOriginalValueReduction.run bits model W k input).1 := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact reduced_replaced_count bits model W k _ _

def MassBound {n : ℕ} (o : Output n) : Prop := o.classified.lightWeight≤o.denominator

theorem reduced_mass_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ)
    (weights : FixedArrayTable n ℕ) (hs : ∑ j,weights.read j=Q) : MassBound (run bits model W k Q weights).1 := by
  have h := GeneralPaperLightFieldIntegerBalance.classified bits model W k Q weights hs
  have hl : (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.lightWeight≤Q := by
    dsimp only at h
    omega
  rw [data]
  unfold specification
  split_ifs <;> exact hl

theorem original_mass_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ) :
    MassBound (GeneralPaperOriginalValueReduction.run bits model W k input).1 := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact reduced_mass_bound bits model W k _ _ (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k input)

theorem original_representatives_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ) :
    0<(GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives := by
  rw [original_representatives]
  exact GeneralPaperLightFieldReduction.representatives_positive k

theorem original_light_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    0<(GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.light.size :=
  lt_trans (original_representatives_positive bits model W k input) (original_replaced_count bits model W k input hReplace)

theorem reciprocal {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ) :
    (1:ℝ)/(GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives=(1/(2:ℝ)^k)/8 := by
  rw [original_representatives]
  unfold GeneralPaperLightFieldReduction.representatives
  push_cast
  ring

theorem quantile_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    ((o.classified.lightWeight:ℝ)/o.denominator)/o.representatives≤(1/(2:ℝ)^k)/8 := by
  dsimp only
  have hQ := (original_first_valid bits model W k input v hv).1
  have hV : ((GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.lightWeight:ℝ)/
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.denominator≤1 := by
    apply (div_le_one (by exact_mod_cast hQ : (0:ℝ)<(GeneralPaperOriginalValueReduction.run bits model W k input).1.denominator)).mpr
    exact_mod_cast original_mass_bound bits model W k input
  have h := div_le_div_of_nonneg_right hV (Nat.cast_nonneg (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
  rw [reciprocal bits model W k input] at h
  exact h

theorem combined_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    GeneralPaperCircleLightPayoff.loss o.classified.lightWeight (GeneralPaperCircleActualWeights.weights o)
        (fun j => (GeneralPaperCircleActualWeights.weights o j:ℝ)/o.denominator)+
      ((o.classified.lightWeight:ℝ)/o.denominator)/o.representatives≤9*(1/(2:ℝ)^k)/40 := by
  have hL := GeneralPaperCircleNativePayoff.loss_bound bits model W k input v hv
    (original_light_positive bits model W k input hReplace)
  have hQ := quantile_bound bits model W k input v hv
  dsimp only at hL hQ ⊢
  unfold GeneralPaperCircleNativePayoff.lightValues at hL
  linarith only [hL,hQ]

end Blotto.GeneralPaperNativeCircleLoss
