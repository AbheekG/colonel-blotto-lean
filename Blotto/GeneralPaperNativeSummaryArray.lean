import Blotto.GeneralPaperSummaryArrayProperties

/-! Reindex the returned array to the native Summary type using the erased
cache-size equality. Its data and price are reused unchanged; no array copy
or source-parameter construction is executed by this type-level transport.
-/
namespace Blotto.GeneralPaperNativeSummaryArray
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def run (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (node : Node height) : Summary k × ℕ :=
  let result := GeneralPaperSummaryArrayExecution.run bits index primitive W c digits height node
  let sizeEq : c.controls.source.summarySize=(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hc]; rfl
  (Eq.mp (congrArg (fun s : ℕ => FixedArrayTable s ℕ) sizeEq) result.1,result.2)

theorem data (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (node : Node height) (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (run bits index primitive W m lambda k Qv c hc digits height node).1=
      GeneralPaperInitialSummary.build c.powers digits (GeneralPaperSourceParameters.prepare k).summarySize height node := by
  subst c
  unfold run
  dsimp only
  rw [GeneralPaperSummaryArrayExecution.data bits index primitive W m lambda k Qv digits height _ rfl node hHeight hValid hPath]
  rfl

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (run true (fun w => w) primitive W m lambda k Qv c hc digits height node).2≤
      GeneralPaperSummaryArrayPrice.profile primitive W m lambda k Qv height :=
  GeneralPaperSummaryArrayPrice.bit_work primitive hMono W m lambda k Qv digits height c hc hDigits node hHeight hValid hPath

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (digits height : ℕ)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height) :
    (run false (fun _ => 1) (fun _ => 1) 1 m lambda k Qv c hc digits height node).2≤
      GeneralPaperSummaryArrayPrice.arithmeticProfile m lambda k Qv height :=
  GeneralPaperSummaryArrayPrice.arithmetic_work m lambda k Qv digits height c hc hDigits node

end Blotto.GeneralPaperNativeSummaryArray
