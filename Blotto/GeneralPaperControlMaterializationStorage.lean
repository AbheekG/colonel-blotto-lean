import Blotto.GeneralPaperSourceControlStorageRates
import Blotto.GeneralPaperProfitGridConstructionStorage

/-! Actual retained control-to-power/grid materialization. Native power
and grid words remain the words used by the existing constructors; outer
retained owners are counted at the caller reference. Every cursor is an
erased observer and the cached constructors execute only once. -/
namespace Blotto.GeneralPaperControlMaterializationStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def powerWord (m lambda k Qv : ℕ) : ℕ := GeneralPaperSourcePreparationControls.word m lambda k Qv

def powerCache (model : RationalCostModel) (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache) :
    GeneralPaperMaterializedPowerCache.Cache :=
  ⟨c,(GeneralPaperCachedPowerPreparation.fromCache model.rat (powerWord m lambda k Qv) k c).1⟩

theorem power_data (model : RationalCostModel) (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    powerCache model m lambda k Qv c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv := by
  dsimp only [powerCache]
  rw [GeneralPaperCachedPowerPreparation.data model.rat _ m lambda k Qv c hc,hc]
  rfl

def gridWord (m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperMaterializedGridCache.localWord (GeneralPaperMaterializedPowerCache.specification m lambda k Qv)

def price (model : RationalCostModel) (m lambda k Qv : ℕ) : ℕ :=
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  (524288*(measure m lambda k Qv+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*
    model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)

def metadataCap (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  m+lambda+k+Qv+price model m lambda k Qv+256*(W+powerWord m lambda k Qv+gridWord m lambda k Qv)+1

def window (model : RationalCostModel) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (columns h copied count : ℕ)
    (hcount : count≤(GeneralPaperProfitGridPrepare.prepare c.profit.qProf c.profit.width c.profit.exponent).size) : ℕ :=
  let U := powerWord m lambda k Qv
  let powers := GeneralPaperCachedPowerPreparation.fromCache model.rat U k c
  let pc := powerCache model m lambda k Qv c
  let V := GeneralPaperMaterializedGridCache.localWord pc
  let grid := GeneralPaperMaterializedGridCache.extend (fun a => a) model.rat V pc
  let result := GeneralPaperMaterializationFromControls.bit model U k c
  GeneralPaperPreparationCacheStorage.footprint W c+
    GeneralPaperMaterializedCacheStorage.powerFootprint W pc+
    GeneralPaperMaterializedCacheStorage.gridFootprint W result.1+
    GeneralPaperPowerConstructionStorage.window model U k c columns+
    (GeneralPaperMaterializedCacheStorage.gridFootprint V grid.1+
      (GeneralPaperMaterializedCacheStorage.powerFootprint V pc+
        GeneralPaperProfitGridConstructionStorage.window model c.profit.qProf c.profit.width c.profit.exponent h copied count hcount))+
    fields W [m,lambda,k,Qv,W,U,V,powers.2,grid.2,result.2,powers.2+grid.2,64*U]+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let U := powerWord m lambda k Qv
  let V := gridWord m lambda k Qv
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  GeneralPaperPreparationCacheStorage.profile W m lambda k Qv+
    GeneralPaperMaterializedCacheStorage.powerProfile W m lambda k Qv+
    GeneralPaperMaterializedCacheStorage.gridProfile W m lambda k Qv+
    GeneralPaperPowerConstructionStorage.profile model U m lambda k Qv+
    (GeneralPaperMaterializedCacheStorage.gridProfile V m lambda k Qv+
      (GeneralPaperMaterializedCacheStorage.powerProfile V m lambda k Qv+
        GeneralPaperProfitGridConstructionStorage.profile model p.qProf p.width p.exponent))+
    12*(natBits (metadataCap model W m lambda k Qv)+W)+288*W

theorem parent_fields (W m lambda k Qv U V P A B R : ℕ) (he : R=A+B+64*U) (hr : R≤P) :
    fields W [m,lambda,k,Qv,W,U,V,A,B,R,A+B,64*U]≤
      12*(natBits (m+lambda+k+Qv+P+256*(W+U+V)+1)+W)+32*W := by
  apply fields_bound W _
  intro z hz
  apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem bounded (model : RationalCostModel) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) (columns h copied count : ℕ)
    (hcolumns : columns≤c.precision.parameters.columns) (hh : h≤c.profit.exponent)
    (hcount : count≤(GeneralPaperProfitGridPrepare.prepare c.profit.qProf c.profit.width c.profit.exponent).size) :
    window model W m lambda k Qv c columns h copied count hcount≤profile model W m lambda k Qv ∧
      (GeneralPaperMaterializationFromControls.bit model (powerWord m lambda k Qv) k c).2≤price model m lambda k Qv := by
  let U := powerWord m lambda k Qv
  let powers := GeneralPaperCachedPowerPreparation.fromCache model.rat U k c
  let pc := powerCache model m lambda k Qv c
  let V := GeneralPaperMaterializedGridCache.localWord pc
  let grid := GeneralPaperMaterializedGridCache.extend (fun a => a) model.rat V pc
  let result := GeneralPaperMaterializationFromControls.bit model U k c
  have hpc := power_data model m lambda k Qv c hc
  change pc=GeneralPaperMaterializedPowerCache.specification m lambda k Qv at hpc
  have hV : V=gridWord m lambda k Qv := congrArg GeneralPaperMaterializedGridCache.localWord hpc
  have hGridData := GeneralPaperMaterializationFromControls.bit_data model U m lambda k Qv c hc
  have hC : GeneralPaperPreparationCacheStorage.footprint W c≤GeneralPaperPreparationCacheStorage.profile W m lambda k Qv := by
    rw [hc];exact GeneralPaperPreparationCacheStorage.native W m lambda k Qv
  have hP : GeneralPaperMaterializedCacheStorage.powerFootprint W pc≤GeneralPaperMaterializedCacheStorage.powerProfile W m lambda k Qv := by
    rw [hpc];exact GeneralPaperMaterializedCacheStorage.power_native W m lambda k Qv
  have hR : GeneralPaperMaterializedCacheStorage.gridFootprint W result.1≤GeneralPaperMaterializedCacheStorage.gridProfile W m lambda k Qv := by
    change GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializationFromControls.bit model U k c).1≤_
    rw [hGridData];exact GeneralPaperMaterializedCacheStorage.grid_native W m lambda k Qv
  have hCols : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns := by rw [hc] at hcolumns;exact hcolumns
  have hPower := GeneralPaperPowerConstructionStorage.bounded model U m lambda k Qv c hc columns hCols
  have hGrid := GeneralPaperProfitGridConstructionStorage.materialized_return model lambda k Qv h copied count pc hpc hh hcount
  have hGridClosed : GeneralPaperMaterializedCacheStorage.gridFootprint V grid.1+
      (GeneralPaperMaterializedCacheStorage.powerFootprint V pc+
        GeneralPaperProfitGridConstructionStorage.window model c.profit.qProf c.profit.width c.profit.exponent h copied count hcount)≤
      GeneralPaperMaterializedCacheStorage.gridProfile (gridWord m lambda k Qv) m lambda k Qv+
        (GeneralPaperMaterializedCacheStorage.powerProfile (gridWord m lambda k Qv) m lambda k Qv+
          GeneralPaperProfitGridConstructionStorage.profile model (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
            (GeneralPaperProfitParameters.parameters m lambda k Qv).width (GeneralPaperProfitParameters.parameters m lambda k Qv).exponent) := by
    apply hGrid.trans_eq
    rw [hpc]
    rfl
  have hWork : result.2≤price model m lambda k Qv := GeneralPaperMaterializationFromControls.bit_work model m lambda k Qv c hc
  have hEq : result.2=powers.2+grid.2+64*U := rfl
  have hf := parent_fields W m lambda k Qv U V (price model m lambda k Qv) powers.2 grid.2 result.2 hEq hWork
  have hCap : metadataCap model W m lambda k Qv=m+lambda+k+Qv+price model m lambda k Qv+256*(W+U+V)+1 := by
    dsimp only [metadataCap,U]
    rw [hV]
  rw [←hCap] at hf
  refine ⟨?_,hWork⟩
  have hCore := Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hC hP) hR) hPower) hGridClosed) hf) (256*W)
  exact hCore.trans_eq (by dsimp only [profile];ring)

theorem returned (model : RationalCostModel) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (columns h copied count : ℕ)
    (hcount : count≤(GeneralPaperProfitGridPrepare.prepare c.profit.qProf c.profit.width c.profit.exponent).size) :
    GeneralPaperMaterializedCacheStorage.gridFootprint W
      (GeneralPaperMaterializationFromControls.bit model (powerWord m lambda k Qv) k c).1≤
      window model W m lambda k Qv c columns h copied count hcount := by
  dsimp only [window]
  omega

end Blotto.GeneralPaperControlMaterializationStorage
