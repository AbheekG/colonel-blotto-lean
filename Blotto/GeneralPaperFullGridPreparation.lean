import Blotto.GeneralPaperProfitGridProfile

/-! One-time source parameter, power-table and profit-grid preparation.
The returned cache is consumed between phases; no constructor is replayed.
Local price/control widths are analytical and are not stored data fields.
-/
namespace Blotto.GeneralPaperFullGridPreparation
open GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 1000000

def prepare (model : RationalCostModel) (m lambda k Qv : ℕ) : GeneralPaperMaterializedGridCache.Cache × ℕ :=
  let W := GeneralPaperSourcePreparationControls.word m lambda k Qv
  let source := GeneralPaperMaterializedPowerCache.prepare model.rat W m lambda k Qv
  let grid := GeneralPaperMaterializedGridCache.extend (fun a => a) model.rat
    (GeneralPaperMaterializedGridCache.localWord source.1) source.1
  (grid.1,source.2+grid.2+32*W)

theorem data (model : RationalCostModel) (m lambda k Qv : ℕ) :
    (prepare model m lambda k Qv).1=GeneralPaperMaterializedGridCache.specification m lambda k Qv := by
  let W := GeneralPaperSourcePreparationControls.word m lambda k Qv
  let source := GeneralPaperMaterializedPowerCache.prepare model.rat W m lambda k Qv
  exact GeneralPaperMaterializedGridCache.data (fun a => a) model.rat
    (GeneralPaperMaterializedGridCache.localWord source.1) m lambda k Qv source.1
    (GeneralPaperMaterializedPowerCache.data model.rat W m lambda k Qv)

def arithmetic (m lambda k Qv : ℕ) : GeneralPaperMaterializedGridCache.Cache × ℕ :=
  let source := GeneralPaperMaterializedPowerCache.arithmetic m lambda k Qv
  let grid := GeneralPaperMaterializedGridCache.extend (fun _ => 1) (fun _ => 1) 1 source.1
  (grid.1,source.2+grid.2+32)

theorem arithmetic_data (m lambda k Qv : ℕ) :
    (arithmetic m lambda k Qv).1=GeneralPaperMaterializedGridCache.specification m lambda k Qv := by
  let source := GeneralPaperMaterializedPowerCache.arithmetic m lambda k Qv
  exact GeneralPaperMaterializedGridCache.data (fun _ => 1) (fun _ => 1) 1 m lambda k Qv source.1
    (GeneralPaperMaterializedPowerCache.arithmetic_data m lambda k Qv)

theorem bit_work (model : RationalCostModel) (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    (prepare model m lambda k Qv).2≤
      (2097152*(measure m lambda k Qv+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*
        model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  let W := GeneralPaperSourcePreparationControls.word m lambda k Qv
  let M := measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let P := model.rat H
  let source := GeneralPaperMaterializedPowerCache.prepare model.rat W m lambda k Qv
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  have hs := GeneralPaperMaterializedPowerCache.bit_work model m lambda k Qv
  have hd := GeneralPaperMaterializedPowerCache.data model.rat W m lambda k Qv
  have hg := GeneralPaperMaterializedGridCache.bit_work model source.1
  have hProfile := GeneralPaperProfitGridProfile.bit_profile model m lambda k Qv
  have hChildProfile : GeneralPaperProfitGridPrice.profile model.rat
      (GeneralPaperMaterializedGridCache.localWord source.1) source.1.controls.profit.qProf
      source.1.controls.profit.width source.1.controls.profit.exponent≤
        GeneralPaperProfitGridProfile.bound p.width p.exponent*P := by
    rw [hd]
    exact hProfile
  have hWord : GeneralPaperMaterializedGridCache.localWord source.1≤P := by
    rw [hd]
    have hw := (GeneralPaperProfitGridEnvelope.widths m lambda k Qv).2.2.1
    change 2*GeneralPaperProfitOrderPrice.word p.width p.exponent≤H at hw
    have hh : GeneralPaperProfitOrderPrice.word p.width p.exponent≤H := by omega
    exact hh.trans (model.word_le H)
  have hW : W≤P := by
    have hw := GeneralPaperSourcePreparationControls.word_le_operand_width m lambda k Qv
    have hWidth : width m lambda k Qv≤H := by dsimp [H,width,GeneralPaperPowerPreparationEnvelope.operandWidth]; omega
    exact (hw.trans hWidth).trans (model.word_le H)
  change source.2≤1048576*M*P at hs
  change source.2+(GeneralPaperMaterializedGridCache.extend (fun a => a) model.rat
    (GeneralPaperMaterializedGridCache.localWord source.1) source.1).2+32*W≤
      (2097152*(M+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*P
  nlinarith only [hs,hg,hChildProfile,hWord,hW,Nat.zero_le (M*P)]

theorem arithmetic_work (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    (arithmetic m lambda k Qv).2≤2097152*(measure m lambda k Qv+1)^2+
      GeneralPaperProfitGridProfile.bound p.width p.exponent := by
  let source := GeneralPaperMaterializedPowerCache.arithmetic m lambda k Qv
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let M := measure m lambda k Qv
  have hs := GeneralPaperMaterializedPowerCache.arithmetic_work m lambda k Qv
  have hg := GeneralPaperMaterializedGridCache.arithmetic_work source.1
  have hProfile : GeneralPaperProfitGridPrice.profile (fun _ => 1) 1 source.1.controls.profit.qProf
      source.1.controls.profit.width source.1.controls.profit.exponent≤GeneralPaperProfitGridProfile.bound p.width p.exponent := by
    rw [GeneralPaperMaterializedPowerCache.arithmetic_data]
    exact GeneralPaperProfitGridProfile.arithmetic_profile p.qProf p.width p.exponent
  change source.2≤1048576*(M+1)^2 at hs
  change source.2+(GeneralPaperMaterializedGridCache.extend (fun _ => 1) (fun _ => 1) 1 source.1).2+32≤
    2097152*(M+1)^2+GeneralPaperProfitGridProfile.bound p.width p.exponent
  nlinarith only [hs,hg,hProfile,Nat.zero_le (M*M)]

theorem same_data (model : RationalCostModel) (m lambda k Qv : ℕ) :
    (prepare model m lambda k Qv).1=(arithmetic m lambda k Qv).1 := by rw [data,arithmetic_data]

end Blotto.GeneralPaperFullGridPreparation
