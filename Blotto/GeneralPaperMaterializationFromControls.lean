import Blotto.GeneralPaperArithmeticSourcePrecall

/-! Materialize powers and profit grid from already returned source
controls. This is the path used after classification: parameter construction
is not called again. Bit and arithmetic power builders stay separate.
-/
namespace Blotto.GeneralPaperMaterializationFromControls
open GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 2000000

def bit (model : RationalCostModel) (W k : ℕ) (c : GeneralPaperSourcePreparationCache.Cache) :
    GeneralPaperMaterializedGridCache.Cache × ℕ :=
  let powers := GeneralPaperCachedPowerPreparation.fromCache model.rat W k c
  let powerCache : GeneralPaperMaterializedPowerCache.Cache := ⟨c,powers.1⟩
  let grid := GeneralPaperMaterializedGridCache.extend (fun a => a) model.rat
    (GeneralPaperMaterializedGridCache.localWord powerCache) powerCache
  (grid.1,powers.2+grid.2+64*W)

theorem bit_data (model : RationalCostModel) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (bit model W k c).1=GeneralPaperMaterializedGridCache.specification m lambda k Qv := by
  apply GeneralPaperMaterializedGridCache.data (fun a => a) model.rat _ m lambda k Qv
    (⟨c,(GeneralPaperCachedPowerPreparation.fromCache model.rat W k c).1⟩ : GeneralPaperMaterializedPowerCache.Cache)
  rw [GeneralPaperCachedPowerPreparation.data model.rat W m lambda k Qv c hc,hc]
  rfl

def arithmetic (k : ℕ) (c : GeneralPaperSourcePreparationCache.Cache) : GeneralPaperMaterializedGridCache.Cache × ℕ :=
  let powers := GeneralPaperCachedPowerPreparation.arithmetic k c
  let powerCache : GeneralPaperMaterializedPowerCache.Cache := ⟨c,powers.1⟩
  let grid := GeneralPaperMaterializedGridCache.extend (fun _ => 1) (fun _ => 1) 1 powerCache
  (grid.1,powers.2+grid.2+64)

theorem arithmetic_data (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (arithmetic k c).1=GeneralPaperMaterializedGridCache.specification m lambda k Qv := by
  apply GeneralPaperMaterializedGridCache.data (fun _ => 1) (fun _ => 1) 1 m lambda k Qv
    (⟨c,(GeneralPaperCachedPowerPreparation.arithmetic k c).1⟩ : GeneralPaperMaterializedPowerCache.Cache)
  rw [GeneralPaperCachedPowerPreparation.arithmetic_data m lambda k Qv c hc,hc]
  rfl

theorem bit_work (model : RationalCostModel) (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    (bit model (GeneralPaperSourcePreparationControls.word m lambda k Qv) k c).2≤
      (524288*(measure m lambda k Qv+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*
        model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  let W := GeneralPaperSourcePreparationControls.word m lambda k Qv
  let M := measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let P := model.rat H
  let powers := GeneralPaperCachedPowerPreparation.fromCache model.rat W k c
  let pc : GeneralPaperMaterializedPowerCache.Cache := ⟨c,powers.1⟩
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  have hp := GeneralPaperPowerPreparationEnvelope.bit_work model m lambda k Qv c hc
  have hd : pc=GeneralPaperMaterializedPowerCache.specification m lambda k Qv := by
    dsimp only [pc,powers]
    rw [GeneralPaperCachedPowerPreparation.data model.rat W m lambda k Qv c hc,hc]
    rfl
  have hg := GeneralPaperMaterializedGridCache.bit_work model pc
  have hProfile : GeneralPaperProfitGridPrice.profile model.rat (GeneralPaperMaterializedGridCache.localWord pc)
      pc.controls.profit.qProf pc.controls.profit.width pc.controls.profit.exponent≤
        GeneralPaperProfitGridProfile.bound p.width p.exponent*P := by
    rw [hd]
    exact GeneralPaperProfitGridProfile.bit_profile model m lambda k Qv
  have hWord : GeneralPaperMaterializedGridCache.localWord pc≤P := by
    rw [hd]
    have hw := (GeneralPaperProfitGridEnvelope.widths m lambda k Qv).2.2.1
    change 2*GeneralPaperProfitOrderPrice.word p.width p.exponent≤H at hw
    exact (show GeneralPaperProfitOrderPrice.word p.width p.exponent≤H by omega).trans (model.word_le H)
  have hW : W≤P := by
    have hw := GeneralPaperSourcePreparationControls.word_le_operand_width m lambda k Qv
    have hs : width m lambda k Qv≤H := by dsimp [H,width,GeneralPaperPowerPreparationEnvelope.operandWidth]; omega
    exact (hw.trans hs).trans (model.word_le H)
  change powers.2≤262144*M*P at hp
  change powers.2+(GeneralPaperMaterializedGridCache.extend (fun a => a) model.rat
    (GeneralPaperMaterializedGridCache.localWord pc) pc).2+64*W≤
      (524288*(M+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*P
  nlinarith only [hp,hg,hProfile,hWord,hW,Nat.zero_le (M*P)]

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    (arithmetic k c).2≤524288*(measure m lambda k Qv+1)^2+GeneralPaperProfitGridProfile.bound p.width p.exponent := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let powers := GeneralPaperCachedPowerPreparation.arithmetic k c
  let pc : GeneralPaperMaterializedPowerCache.Cache := ⟨c,powers.1⟩
  let M := measure m lambda k Qv
  have hp := (GeneralPaperCachedPowerPreparation.arithmetic_work m lambda k Qv c hc).trans
    (GeneralPaperPowerPreparationEnvelope.arithmetic_profile m lambda k Qv)
  have hg := GeneralPaperMaterializedGridCache.arithmetic_work pc
  have hd : pc=GeneralPaperMaterializedPowerCache.specification m lambda k Qv := by
    dsimp only [pc,powers]
    rw [GeneralPaperCachedPowerPreparation.arithmetic_data m lambda k Qv c hc,hc]
    rfl
  have hProfile : GeneralPaperProfitGridPrice.profile (fun _ => 1) 1 pc.controls.profit.qProf
      pc.controls.profit.width pc.controls.profit.exponent≤GeneralPaperProfitGridProfile.bound p.width p.exponent := by
    rw [hd]
    exact GeneralPaperProfitGridProfile.arithmetic_profile p.qProf p.width p.exponent
  change powers.2≤262144*(M+1)^2 at hp
  change powers.2+(GeneralPaperMaterializedGridCache.extend (fun _ => 1) (fun _ => 1) 1 pc).2+64≤
    524288*(M+1)^2+GeneralPaperProfitGridProfile.bound p.width p.exponent
  nlinarith only [hp,hg,hProfile,Nat.zero_le (M*M)]

theorem same_data (model : RationalCostModel) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (bit model W k c).1=(arithmetic k c).1 := by rw [bit_data _ _ _ _ _ _ _ hc,arithmetic_data _ _ _ _ _ hc]

end Blotto.GeneralPaperMaterializationFromControls
