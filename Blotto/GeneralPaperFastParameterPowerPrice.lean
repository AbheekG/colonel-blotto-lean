import Blotto.GeneralPaperActualFastOrderedDPPrice

/-! Fast-rational prices for the actual parameter and power constructors.
The short operand width is the previously derived constant multiple of M.
Native controls close the calibrated word premise; actual cache identities
remain unchanged. These are paper-model prices, not physical runtime claims. -/
namespace Blotto.GeneralPaperFastParameterPowerPrice
open GeneralPaperFastRationalModel GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 1000000

def parameterProfile (C d W m lambda k Qv : ℕ) : ℕ :=
  262144*measure m lambda k Qv*(W+charge C d (width m lambda k Qv))

theorem parameter_work {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv : ℕ) :
    (GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).2≤parameterProfile C d W m lambda k Qv :=
  (GeneralPaperSourcePreparationEnvelope.work model.rat model.monotone W m lambda k Qv).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hg _) W))

theorem parameter_calibrated {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (m lambda k Qv : ℕ) :
    (GeneralPaperSourcePreparationCache.prepare model.rat (GeneralPaperSourcePreparationControls.word m lambda k Qv) m lambda k Qv).2≤
      2147483648*C*(measure m lambda k Qv)^2*logFactor d (width m lambda k Qv) := by
  let M := measure m lambda k Qv
  let H := width m lambda k Qv
  let W := GeneralPaperSourcePreparationControls.word m lambda k Qv
  have hn := GeneralPaperSourcePreparationEnvelope.work model.rat model.monotone W m lambda k Qv
  have hw : W≤model.rat H :=
    (GeneralPaperSourcePreparationControls.word_le_operand_width m lambda k Qv).trans (model.word_le H)
  have hgH := hg H
  calc
    _≤262144*M*(W+model.rat H) := hn
    _≤262144*M*(2*charge C d H) := Nat.mul_le_mul_left (262144*M) (by omega)
    _=524288*M*charge C d H := by ring
    _=2147483648*C*M^2*logFactor d H := by dsimp only [charge,H,width]; ring

def powerProfile (C d W m lambda k Qv : ℕ) : ℕ :=
  131072*measure m lambda k Qv*(W+charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))

theorem power_work {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (GeneralPaperCachedPowerPreparation.fromCache model.rat W k c).2≤powerProfile C d W m lambda k Qv :=
  (GeneralPaperPowerPreparationEnvelope.work model.rat model.monotone W m lambda k Qv c hc).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hg _) W))

theorem power_calibrated {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (GeneralPaperCachedPowerPreparation.fromCache model.rat (GeneralPaperSourcePreparationControls.word m lambda k Qv) k c).2≤
      274877906944*C*(measure m lambda k Qv)^2*
        logFactor d (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  have hn := GeneralPaperPowerPreparationEnvelope.bit_work model m lambda k Qv c hc
  have hgH := Nat.mul_le_mul_left (262144*measure m lambda k Qv)
    (hg (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))
  exact hn.trans (hgH.trans_eq (by dsimp only [charge,GeneralPaperPowerPreparationEnvelope.operandWidth]; ring))

theorem grid_profile {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    GeneralPaperProfitGridPrice.profile model.rat (GeneralPaperProfitOrderPrice.word p.width p.exponent) p.qProf p.width p.exponent≤
      GeneralPaperProfitGridProfile.bound p.width p.exponent*charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :=
  (GeneralPaperProfitGridProfile.bit_profile model m lambda k Qv).trans (Nat.mul_le_mul_left _ (hg _))

theorem grid_work {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    (GeneralPaperProfitGridPrice.run (fun x => x) model.rat (GeneralPaperProfitOrderPrice.word p.width p.exponent) p.qProf p.width p.exponent).2≤
      GeneralPaperProfitGridProfile.bound p.width p.exponent*charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :=
  (GeneralPaperProfitGridPrice.bit_work model _ _ _).trans (grid_profile hg m lambda k Qv)

theorem materialization {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    (GeneralPaperMaterializationFromControls.bit model (GeneralPaperSourcePreparationControls.word m lambda k Qv) k c).2≤
      (524288*(measure m lambda k Qv+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*
        charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :=
  (GeneralPaperMaterializationFromControls.bit_work model m lambda k Qv c hc).trans (Nat.mul_le_mul_left _ (hg _))

end Blotto.GeneralPaperFastParameterPowerPrice
