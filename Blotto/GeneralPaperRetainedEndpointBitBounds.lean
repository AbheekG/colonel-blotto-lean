import Blotto.GeneralPaperRetainedBasisEndpointBits
import Blotto.GeneralPaperEndpointRatioSize

/-! Bounds for the actual constructed endpoint fraction and reached
guard/reciprocal prices. Unreduced root/grid integers stay below qbar;
these are proofs about retained data, not rational-encoding queries. -/
namespace Blotto.GeneralPaperRetainedEndpointBitBounds
open GeneralPaperProxyParameters GeneralPaperRetainedBasisEndpoint GeneralPaperRetainedBasisEndpointBits
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem fraction_bounds (primitive : ℕ → ℕ) (W m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) :
    let endpoint := (GeneralPaperRetainedEndpointFraction.run primitive W (prepare m k).Qg (grid_positive m k)
      (GeneralPaperProxyClassifier.classify m k b)).1
    endpoint.num≤(prepare m k).qbar ∧ endpoint.den≤(prepare m k).qbar := by
  let endpoint := (GeneralPaperRetainedEndpointFraction.run primitive W (prepare m k).Qg (grid_positive m k)
    (GeneralPaperProxyClassifier.classify m k b)).1
  have hH : (prepare m k).H≤(prepare m k).qbar := by
    rw [(GeneralPaperProxyParameters.data m k).2.2.2.2.2.2]
    have hg := grid_lower m k
    have hp := H_positive m k
    nlinarith
  have hGrid : (prepare m k).Qg≤(prepare m k).qbar := by
    rw [(GeneralPaperProxyParameters.data m k).2.2.2.2.2.2]
    omega
  have hd : endpoint.den≤(prepare m k).qbar := by
    dsimp only [endpoint,GeneralPaperRetainedEndpointFraction.run]
    rw [ite_eq_right hModify]
    cases hr : (GeneralPaperProxyClassifier.classify m k b).root with
    | none => dsimp only; split <;> exact hGrid
    | some f => dsimp only; exact (GeneralPaperProxyClassifier.root_sound m k b f hr).1.trans hH
  have hv := GeneralPaperRetainedEndpointFraction.actual_value primitive W m k b
  have hu := (GeneralPaperProxyEndpointBounds.endpoint_unit m k b hb hModify).2
  have he : endpoint.value≤1 := by rw [←hv] at hu; exact hu
  have hn : endpoint.num≤endpoint.den := by
    have hPos : (0:ℚ)<endpoint.den := by exact_mod_cast endpoint.den_pos
    have hh := (div_le_one hPos).mp he
    exact_mod_cast hh
  exact ⟨hn.trans hd,hd⟩

theorem transformed_bounds (primitive : ℕ → ℕ) (W m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) (reciprocal : Bool) :
    let endpoint := (GeneralPaperRetainedEndpointFraction.run primitive W (prepare m k).Qg (grid_positive m k)
      (GeneralPaperProxyClassifier.classify m k b)).1
    (numerator endpoint reciprocal).natAbs≤(prepare m k).qbar ∧ denominator endpoint reciprocal≤(prepare m k).qbar := by
  have hh := fraction_bounds primitive W m k b hb hModify
  cases reciprocal with
  | false => simpa only [numerator,denominator,Bool.false_eq_true,ite_false,Int.natAbs_natCast] using hh
  | true => simpa only [numerator,denominator,ite_true,Int.natAbs_natCast] using And.symm hh

def priceWidth (B : ℕ) : ℕ := 1+2*(binaryWordWidth B+1)

theorem guard_price (model : RationalCostModel) (W B : ℕ) (value : ℚ)
    (hValue : RationalHeight value (binaryWordWidth B)) :
    guardPrice model W value≤model.rat (priceWidth B)+32*W := by
  have hV := (rationalWordWidth_of_height hValue).trans (show 1+2*binaryWordWidth B≤priceWidth B by unfold priceWidth; omega)
  have hZ := rationalWordWidth_of_height (GeneralPaperQuantizedHeight.zero_height (binaryWordWidth B) (binaryWordWidth_pos B))
  have hZero := hZ.trans (show 1+2*binaryWordWidth B≤priceWidth B by unfold priceWidth; omega)
  exact Nat.add_le_add_right (model.monotone (max_le hV hZero)) _

theorem endpoint_price (model : RationalCostModel) (W B : ℕ) (endpoint : Farey.Fraction) (value : ℚ)
    (hNum : endpoint.num≤B) (hDen : endpoint.den≤B) (hValue : RationalHeight value (binaryWordWidth B))
    (reciprocal : Bool) : endpointPrice model W endpoint value reciprocal≤6*model.rat (priceWidth B)+32*W := by
  let Q := model.rat (priceWidth B)
  have hPromote : 1+binaryWordWidth B≤priceWidth B := by unfold priceWidth; omega
  have hNumP := model.monotone ((Nat.add_le_add_left (binaryWordWidth_mono hNum) 1).trans hPromote)
  have hDenP := model.monotone ((Nat.add_le_add_left (binaryWordWidth_mono hDen) 1).trans hPromote)
  have hTop : (numerator endpoint reciprocal).natAbs≤B := by cases reciprocal <;> exact (by first | exact hNum | exact hDen)
  have hBottom : denominator endpoint reciprocal≤B := by cases reciprocal <;> exact (by first | exact hDen | exact hNum)
  have hTopP := model.monotone ((GeneralPaperIntegerPrimitivePrice.word_bound _ B hTop).trans hPromote)
  have hBottomP := model.monotone ((Nat.add_le_add_left (binaryWordWidth_mono hBottom) 1).trans hPromote)
  have hV := (rationalWordWidth_of_height hValue).trans (show 1+2*binaryWordWidth B≤priceWidth B by unfold priceWidth; omega)
  have hOne : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
  have hOne' := hOne.mono (show 1≤binaryWordWidth B+1 by omega)
  have hOneW := (rationalWordWidth_of_height hOne').trans (show 1+2*(binaryWordWidth B+1)≤priceWidth B by rfl)
  have hDiv := rationalWordWidth_of_height (hOne.div hValue)
  have hDiv' : rationalWordWidth ((1:ℚ)/value)≤priceWidth B := by dsimp only [priceWidth]; omega
  have hDivP := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun x y => x/y)
    1 value (priceWidth B) hOneW hV hDiv'
  have hVP := model.monotone hV
  unfold endpointPrice
  split <;> change _≤6*Q+32*W <;> omega

end Blotto.GeneralPaperRetainedEndpointBitBounds
