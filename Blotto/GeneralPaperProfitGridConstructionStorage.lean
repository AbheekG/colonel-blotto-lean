import Blotto.GeneralPaperGridArrayConstructionStorage

/-! Full native grid-construction reservation: generation/order, packing,
scaled prefixes, depth construction, returned grid and raw scalar records.
The local reference word is the one derived and used by the actual grid
constructor. Final global-address calibration remains a separate join. -/
namespace Blotto.GeneralPaperProfitGridConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem inputs (W q w B : ℕ) : fields W [q,w,B]≤3*(GeneralPaperEncodedProfitGrid.word q w B+W)+32*W := by
  have hw := binaryWordWidth_mono (Nat.le_add_right w 1)
  have hb := GeneralPaperInitializerControlCounters.word_le_self B
  apply fields_bound W _
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> unfold natBits GeneralPaperEncodedProfitGrid.word <;> omega

def window (model : RationalCostModel) (q w B h copied count : ℕ)
    (hc : count≤(GeneralPaperProfitGridPrepare.prepare q w B).size) : ℕ :=
  let W := GeneralPaperProfitOrderPrice.word w B
  let g := GeneralPaperProfitGridPrepare.prepare q w B
  GeneralPaperProfitOrderConstructionStorage.window model W w B h copied+
    GeneralPaperGridArrayConstructionStorage.packingWindow W copied (GeneralPaperProfitGridPrepare.ordered w B)+
    2*GeneralPaperGridArrayConstructionStorage.scaledPrefix (fun a => a) model.rat W q g.numerators count hc+
    GeneralPaperGridArrayConstructionStorage.frames W g.size+
    GeneralPaperCeilingConstructionStorage.peak W (g.size+1) 1 (by decide)+
    2*GeneralPaperEncodedProfitGrid.footprint W g+fields W [q,w,B]+
    (GeneralPaperProfitGridPrice.run (fun a => a) model.rat W q w B).2

def profile (model : RationalCostModel) (q w B : ℕ) : ℕ :=
  let W := GeneralPaperProfitOrderPrice.word w B
  let g := GeneralPaperProfitGridPrepare.prepare q w B
  let n := g.size
  let P := GeneralPaperEncodedProfitGrid.word q w B
  let U := 2*denominator w B
  GeneralPaperProfitOrderConstructionStorage.profile model W w B+
    (n*(natBits U+2*W)+32*W+2*(n*(natBits U+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W n+128*W)+
    2*(n*(P+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W n+
    (binaryWordWidth (n+1)+1)*(5*GeneralPaperCeilingConstructionStorage.word (n+1)+192*W)+
    2*GeneralPaperEncodedProfitGrid.profile W P w B+(3*(P+W)+32*W)+
    GeneralPaperProfitGridPrice.profile model.rat W q w B

theorem bounded (model : RationalCostModel) (q w B h copied count : ℕ)
    (hc : count≤(GeneralPaperProfitGridPrepare.prepare q w B).size) (hh : h≤B) :
    window model q w B h copied count hc≤profile model q w B := by
  let W := GeneralPaperProfitOrderPrice.word w B
  let g := GeneralPaperProfitGridPrepare.prepare q w B
  have a := GeneralPaperProfitOrderConstructionStorage.bounded model W w B h copied hh
  have b := GeneralPaperGridArrayConstructionStorage.packing_window W (2*denominator w B) copied
    (GeneralPaperProfitGridPrepare.ordered w B) (GeneralPaperSortedBreakpoints.ordered_bound _ _)
  have c := GeneralPaperGridArrayConstructionStorage.scaled_bound (fun a => a) model.rat W q w B g.numerators
    (GeneralPaperProfitGridPrepare.numerator_bound q w B) count hc
  have hCeiling := GeneralPaperCeilingConstructionStorage.bounded W (g.size+1) 1 (by decide) (by omega)
  have hDepth := GeneralPaperPowerCeiling.loop_depth (g.size+1) 1 (by decide)
  have d := hCeiling.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hDepth 1))
  have e := GeneralPaperEncodedProfitGrid.native W q w B
  have f := inputs W q w B
  have hs := GeneralPaperProfitGridPrice.bit_work model q w B
  have hCore := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add a b) (Nat.mul_le_mul_left 2 c))
      (GeneralPaperGridArrayConstructionStorage.frames W g.size)) d)
    (Nat.mul_le_mul_left 2 e)) f) hs
  exact hCore.trans_eq (by unfold profile; rfl)

theorem returned (model : RationalCostModel) (q w B : ℕ) :
    let W := GeneralPaperProfitOrderPrice.word w B
    GeneralPaperEncodedProfitGrid.footprint W (GeneralPaperProfitGridPrice.run (fun a => a) model.rat W q w B).1≤
      GeneralPaperEncodedProfitGrid.profile W (GeneralPaperEncodedProfitGrid.word q w B) w B := by
  dsimp only
  rw [GeneralPaperProfitGridPrice.data]
  exact GeneralPaperEncodedProfitGrid.native _ q w B

theorem materialized {m : ℕ} (model : RationalCostModel) (lambda k Qv h copied count : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hh : h≤c.controls.profit.exponent)
    (hcount : count≤(GeneralPaperProfitGridPrepare.prepare c.controls.profit.qProf c.controls.profit.width c.controls.profit.exponent).size) :
    let W := GeneralPaperMaterializedGridCache.localWord c
    GeneralPaperMaterializedCacheStorage.powerFootprint W c+
      window model c.controls.profit.qProf c.controls.profit.width c.controls.profit.exponent h copied count hcount≤
      GeneralPaperMaterializedCacheStorage.powerProfile W m lambda k Qv+
        profile model c.controls.profit.qProf c.controls.profit.width c.controls.profit.exponent := by
  have hCache : GeneralPaperMaterializedCacheStorage.powerFootprint (GeneralPaperMaterializedGridCache.localWord c) c≤
      GeneralPaperMaterializedCacheStorage.powerProfile (GeneralPaperMaterializedGridCache.localWord c) m lambda k Qv := by
    rw [hc]
    exact GeneralPaperMaterializedCacheStorage.power_native _ m lambda k Qv
  exact Nat.add_le_add hCache (bounded model _ _ _ h copied count hcount hh)

theorem materialized_return {m : ℕ} (model : RationalCostModel) (lambda k Qv h copied count : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hh : h≤c.controls.profit.exponent)
    (hcount : count≤(GeneralPaperProfitGridPrepare.prepare c.controls.profit.qProf c.controls.profit.width c.controls.profit.exponent).size) :
    let W := GeneralPaperMaterializedGridCache.localWord c
    GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializedGridCache.extend (fun a => a) model.rat W c).1+
      (GeneralPaperMaterializedCacheStorage.powerFootprint W c+
        window model c.controls.profit.qProf c.controls.profit.width c.controls.profit.exponent h copied count hcount)≤
      GeneralPaperMaterializedCacheStorage.gridProfile W m lambda k Qv+
        (GeneralPaperMaterializedCacheStorage.powerProfile W m lambda k Qv+
          profile model c.controls.profit.qProf c.controls.profit.width c.controls.profit.exponent) :=
  Nat.add_le_add (GeneralPaperMaterializedCacheStorage.grid_returned (fun a => a) model.rat _ m lambda k Qv c hc)
    (materialized model lambda k Qv h copied count c hc hh hcount)

end Blotto.GeneralPaperProfitGridConstructionStorage
