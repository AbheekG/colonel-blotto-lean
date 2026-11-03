import Blotto.GeneralPaperRetainedPairSource

/-! Execute the source with its retained epoch count, then decode/check
its full table once. T is a retained row count, with an erased equality.
No trajectory parameter constructor is evaluated on this data path. -/
namespace Blotto.GeneralPaperRetainedSourceRows
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperSourceRowsExecution
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem produced_size {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br) :
    (GeneralPaperGeometricSourceExecution.run bits (index bits) model W k Qv a c hc shared shared.trajectory.epochs).1.2.size=
      shared.trajectory.rows := by
  subst shared
  exact GeneralPaperSourceRowsDriver.produced_size bits model W k Qv a c hc weights Bc Br _ rfl

def run {m T : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=T) : (FixedArrayTable T (FixedArrayTable m ℚ)×Bool)×ℕ :=
  let source := GeneralPaperGeometricSourceExecution.run bits (index bits) model W k Qv a c hc shared shared.trajectory.epochs
  let codes : FixedArrayTable T (FixedArrayTable m ℕ) :=
    ⟨source.1.2,(produced_size bits model W k Qv a c hc weights Bc Br shared hs).trans hT⟩
  let returned := GeneralPaperSourceRowsExecution.run bits model W a codes shared.Bc
  (returned.1,source.2+returned.2+64*address bits W shared.trajectory.epochs)

theorem data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    run bits model W k Qv a c hc weights Bc Br shared hs hT=
      GeneralPaperSourceRowsDriver.run bits model W k Qv a c hc weights Bc Br shared hs := by
  subst shared
  rfl

end Blotto.GeneralPaperRetainedSourceRows
