import Blotto.GeneralPaperCircleLightPayoff

/-! The actual retained first-round light values discharge the circle
payoff error bound e/10. Original weights/maps, light mass and positivity
are observed from the native return; none is supplied as a lifting oracle. -/
namespace Blotto.GeneralPaperCircleNativePayoff
open GeneralPaperCircleActualWeights
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def Small {n : ℕ} (k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : Prop :=
  ∀ j:Fin o.classified.light.size,(weights o j:ℚ)/o.denominator≤GeneralPaperLightFieldReduction.accuracy k/10

theorem reduced_small {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q) (w : FixedArrayTable n ℕ) :
    Small k (GeneralPaperReducedValuesDriver.run bits model W k Q w).1 := by
  have h : ∀ j:Fin (GeneralPaperLightFieldClassification.run bits model W k Q w).1.1.light.size,
      (w.read (GeneralPaperLightFieldOrder.index (GeneralPaperLightFieldClassification.run bits model W k Q w).1.1.light j):ℚ)/Q≤
        GeneralPaperLightFieldReduction.accuracy k/10 := by
    intro j
    exact GeneralPaperLightFieldClassification.light_entry bits model W k Q hQ w _ (Array.getElem_mem j.isLt)
  rw [GeneralPaperReducedValuesDriver.data]
  unfold GeneralPaperReducedValuesDriver.specification
  split_ifs <;> exact h

theorem original_small {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    Small k (GeneralPaperOriginalValueReduction.run bits model W k values).1 := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact reduced_small bits model W k _
    (GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv).1 _

noncomputable def lightValues {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) : Fin o.classified.light.size → ℝ :=
  fun j => (weights o j:ℝ)/o.denominator

theorem lightValues_nonnegative {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) (j : Fin o.classified.light.size) :
    0≤lightValues o j := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem lightValues_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (j : Fin (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size) :
    lightValues (GeneralPaperOriginalValueReduction.run bits model W k values).1 j≤(1/(2:ℝ)^k)/10 := by
  have h := original_small bits model W k values v hv j
  have hr : (((weights (GeneralPaperOriginalValueReduction.run bits model W k values).1 j:ℚ)/
      (GeneralPaperOriginalValueReduction.run bits model W k values).1.denominator:ℚ):ℝ)≤
      ((GeneralPaperLightFieldReduction.accuracy k/10:ℚ):ℝ) := by exact_mod_cast h
  simpa only [GeneralPaperLightFieldReduction.accuracy,Rat.cast_div,Rat.cast_natCast,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,
    lightValues] using hr

theorem loss_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hg : 0<(GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    GeneralPaperCircleLightPayoff.loss o.classified.lightWeight (weights o) (lightValues o)≤(1/(2:ℝ)^k)/10 := by
  exact GeneralPaperCircleLightPayoff.loss_le_max _ (original_total_positive bits model W k values v hv hg) _
    (original_sum bits model W k values) _ _ (lightValues_bound bits model W k values v hv)

theorem original_error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hg : 0<(GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size)
    (y : Fin (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size → ℝ)
    (x : Fin (GeneralPaperLightFieldReduction.representatives k) → ℝ) (hx : Monotone x) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let hR := GeneralPaperLightFieldReduction.representatives_positive k
    let hL := original_total_positive bits model W k values v hv hg
    0≤GeneralPaperCircleLightPayoff.reconstructed _ _ hR hL (weights o) (lightValues o) y x-
        GeneralPaperCircleLightPayoff.comparison (GeneralPaperLightFieldReduction.representatives k) o.classified.lightWeight (weights o) (lightValues o) y x ∧
      GeneralPaperCircleLightPayoff.reconstructed _ _ hR hL (weights o) (lightValues o) y x-
        GeneralPaperCircleLightPayoff.comparison (GeneralPaperLightFieldReduction.representatives k) o.classified.lightWeight (weights o) (lightValues o) y x≤(1/(2:ℝ)^k)/10 := by
  exact GeneralPaperCircleLightPayoff.error_le_max _ _ _ _ _ (original_sum bits model W k values) _
    (lightValues_nonnegative _) _ (lightValues_bound bits model W k values v hv) y x hx

end Blotto.GeneralPaperCircleNativePayoff
