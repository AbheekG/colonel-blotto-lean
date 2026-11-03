import Blotto.GeneralPaperSummaryArrayPrice

/-! The priced array retains all occurrences and inherits the native code,
ordering and CDF certificates. These equalities introduce no extra pass.
-/
namespace Blotto.GeneralPaperSummaryArrayProperties
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem codes (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) (r : Fin c.controls.source.summarySize) :
    (run bits index primitive W c digits height node).1.read r<2^height := by
  rw [data bits index primitive W m lambda k Qv digits height c hc node hHeight hValid hPath]
  exact GeneralPaperInitialSummary.code_bounds _ _ _ _ _ r

theorem ordered (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    Monotone (run bits index primitive W c digits height node).1.read := by
  subst c
  subst digits
  rw [data bits index primitive W m lambda k Qv _ height _ rfl node hHeight hValid hPath]
  exact GeneralPaperSummaryOrdered.summary_ordered lambda k height node hHeight hValid hPath

theorem cdf_error (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) (cut : ℕ) (hCut : cut≤2^height) :
    |GeneralPaperQuantileOccurrenceCount.summaryCDF (run bits index primitive W c digits height node).1.read cut-
      GeneralPaperQuantileSearch.cdf k node cut|<(GeneralPaperSourceParameters.prepare k).nu := by
  subst c
  subst digits
  rw [data bits index primitive W m lambda k Qv _ height _ rfl node hHeight hValid hPath]
  exact GeneralPaperInitialSummary.cdf_error lambda k height node hHeight hValid hPath cut hCut

end Blotto.GeneralPaperSummaryArrayProperties
