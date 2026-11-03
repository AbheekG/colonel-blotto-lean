import Blotto.GeneralPaperProfitGridEnvelope

/-! Extend the returned parameter/power cache with the complete profit
grid. The extension reuses the retained parameter record and power table.
No source, trajectory, profit-parameter or precision constructor is replayed.
-/
namespace Blotto.GeneralPaperMaterializedGridCache
set_option autoImplicit false
set_option maxHeartbeats 8000000

structure Cache where
  source : GeneralPaperMaterializedPowerCache.Cache
  profit : GeneralPaperProfitParameters.Prepared

def specification (m lambda k Qv : ℕ) : Cache :=
  ⟨GeneralPaperMaterializedPowerCache.specification m lambda k Qv,GeneralPaperProfitParameters.prepare m lambda k Qv⟩

def extend (index primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) : Cache × ℕ :=
  let p := c.controls.profit
  let grid := GeneralPaperProfitGridPrice.run index primitive W p.qProf p.width p.exponent
  (⟨c,⟨p,grid.1⟩⟩,grid.2+64*W)

theorem data (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) :
    (extend index primitive W c).1=specification m lambda k Qv := by
  subst c
  simp only [extend,GeneralPaperProfitGridPrice.data]
  rfl

def localWord (c : GeneralPaperMaterializedPowerCache.Cache) : ℕ :=
  GeneralPaperProfitOrderPrice.word c.controls.profit.width c.controls.profit.exponent

theorem bit_work (model : RationalCostModel) (c : GeneralPaperMaterializedPowerCache.Cache) :
    (extend (fun a => a) model.rat (localWord c) c).2≤
      GeneralPaperProfitGridPrice.profile model.rat (localWord c) c.controls.profit.qProf
        c.controls.profit.width c.controls.profit.exponent+64*localWord c := by
  exact Nat.add_le_add_right (GeneralPaperProfitGridPrice.bit_work model _ _ _) _

theorem arithmetic_work (c : GeneralPaperMaterializedPowerCache.Cache) :
    (extend (fun _ => 1) (fun _ => 1) 1 c).2≤
      GeneralPaperProfitGridPrice.profile (fun _ => 1) 1 c.controls.profit.qProf
        c.controls.profit.width c.controls.profit.exponent+64 := by
  exact Nat.add_le_add_right (GeneralPaperProfitGridPrice.arithmetic_work _ _ _) _

theorem same_data (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) :
    (extend index primitive W c).1=(extend (fun _ => 1) (fun _ => 1) 1 c).1 := by rw [data _ _ _ _ _ _ _ _ hc,data _ _ _ _ _ _ _ _ hc]

theorem returned_parameters (index primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) :
    (extend index primitive W c).1.source=c ∧ (extend index primitive W c).1.profit.parameters=c.controls.profit := ⟨rfl,rfl⟩

theorem returned_grid (index primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) :
    let p := c.controls.profit
    (extend index primitive W c).1.profit.grid=GeneralPaperProfitGridPrepare.prepare p.qProf p.width p.exponent :=
  GeneralPaperProfitGridPrice.data _ _ _ _ _ _

end Blotto.GeneralPaperMaterializedGridCache
