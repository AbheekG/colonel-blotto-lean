import Blotto.GeneralPaperActualQuantileSearch

/-! Each target index is incremented once, searched once and stored by
reference once. Repeated codes retain distinct occurrence slots. The native
summary work sum is analytical and is not executed as another array pass.
Array word calibration is likewise erased analysis, not input decoding.
-/
namespace Blotto.GeneralPaperSummaryArrayExecution
open GeneralPaperIntervalCache
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def arrayWord (W count : ℕ) : ℕ := W+64+8*binaryWordWidth (count+1)

def element (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits height : ℕ) (node : Node height) (r : Fin c.controls.source.summarySize) : ℕ × ℕ :=
  let target := r.val+1
  let answer := GeneralPaperQuantileSearchExecution.run bits primitive W c digits target height node
  (answer.1.location,answer.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) r.val 1+32*W)

def run (bits : Bool) (index primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits height : ℕ) (node : Node height) : FixedArrayTable c.controls.source.summarySize ℕ × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W c.controls.source.summarySize else W)
    (element bits primitive W c digits height node)

theorem element_data (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (r : Fin c.controls.source.summarySize) :
    (element bits primitive W c digits height node r).1=
      (GeneralPaperQuantileSearch.search c.powers digits (r.val+1) c.controls.source.summarySize height node).location := by
  unfold element
  dsimp only
  rw [GeneralPaperQuantileSearchExecution.data bits primitive W m lambda k Qv digits (r.val+1) height c hc node hHeight hValid hPath]

theorem data (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (run bits index primitive W c digits height node).1=
      GeneralPaperInitialSummary.build c.powers digits c.controls.source.summarySize height node := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]
  unfold GeneralPaperInitialSummary.build
  congr 1
  funext r
  exact element_data bits primitive W m lambda k Qv digits height c hc node hHeight hValid hPath r

theorem every_prefix (bits : Bool) (index primitive : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (digits height : ℕ) (node : Node height)
    (count : ℕ) (hCount : count≤c.controls.source.summarySize) :
    (PaperIndexedArrayConstruction.fill index (if bits then arrayWord W c.controls.source.summarySize else W)
      (element bits primitive W c digits height node) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperSummaryArrayExecution
