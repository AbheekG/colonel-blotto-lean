import Blotto.GeneralPaperGeometricSourceStepPrice

/-! Sum the actually executed source steps. Actual selected callers below
derive the step premise; there is no cost callback in the implementation. -/
namespace Blotto.GeneralPaperGeometricSourceLoopPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperGeometricSourceExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem work {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (I E count : ℕ)
    (hInitial : (run bits index model W k Qv a c hc shared 0).2≤I)
    (hSteps : ∀ time<count,(step bits index model W k Qv a c hc shared time (run bits index model W k Qv a c hc shared time).1).2≤E) :
    (run bits index model W k Qv a c hc shared count).2≤I+count*E := by
  induction count with
  | zero => simpa only [Nat.zero_mul,Nat.add_zero] using hInitial
  | succ count ih =>
    have hp := ih (fun time ht => hSteps time (by omega))
    have hs := hSteps count (by omega)
    rw [run_succ]
    dsimp only
    nlinarith only [hp,hs]

end Blotto.GeneralPaperGeometricSourceLoopPrice
