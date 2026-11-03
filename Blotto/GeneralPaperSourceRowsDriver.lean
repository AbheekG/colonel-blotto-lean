import Blotto.GeneralPaperSourceRowsRates

/-! The complete source-to-rational-row driver runs the geometric source
once on the retained prepared shared state, discards its forest, and decodes
and checks the returned full code table once. Cache/size identities erase. -/
namespace Blotto.GeneralPaperSourceRowsDriver
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperSourceRowsExecution
open GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem produced_size {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m)
    (hs : shared=prepare a k Qv weights Bc Br) :
    (GeneralPaperGeometricSourceExecution.run bits (index bits) model W k Qv a c hc shared
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).1.2.size=
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows := by
  rw [hs]
  exact (GeneralPaperGeometricSourceExecution.size bits (index bits) model W k Qv a c hc weights Bc Br
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs le_rfl).trans
      (GeneralPaperTrajectoryParameters.rows_product a.lambda k).symm

def run {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m)
    (hs : shared=prepare a k Qv weights Bc Br) :
    (FixedArrayTable (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows (FixedArrayTable m ℚ) × Bool) × ℕ :=
  let source := GeneralPaperGeometricSourceExecution.run bits (index bits) model W k Qv a c hc shared
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs
  let codes : FixedArrayTable (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows (FixedArrayTable m ℕ) :=
    ⟨source.1.2,produced_size bits model W k Qv a c hc weights Bc Br shared hs⟩
  let returned := GeneralPaperSourceRowsExecution.run bits model W a codes shared.Bc
  (returned.1,source.2+returned.2+64*address bits W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)

theorem data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m)
    (hs : shared=prepare a k Qv weights Bc Br) :
    (run bits model W k Qv a c hc weights Bc Br shared hs).1=
      (GeneralPaperSourceRowsExecution.run bits model W a
        (GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br) Bc).1 := by
  subst shared
  have ht := GeneralPaperSourceRowsContract.native_table bits model W k Qv a c hc weights Bc Br
    _ rfl (produced_size bits model W k Qv a c hc weights Bc Br _ rfl)
  unfold run
  dsimp only
  rw [ht]
  rfl

theorem rational_data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m)
    (hs : shared=prepare a k Qv weights Bc Br) :
    (run bits model W k Qv a c hc weights Bc Br shared hs).1.1=
      GeneralPaperCatalogueRationalTrajectory.rows a k Qv qbar weights Bc Br := by
  rw [data]
  exact GeneralPaperSourceRowsContract.source_data bits model W k Qv qbar a weights Bc Br

theorem checked {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv q qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m)
    (hs : shared=prepare a k Qv weights Bc Br) (hm : 0<m) (hQv : 0<Qv)
    (hw : ∑ j,weights.read j=Qv) (hB : 0≤Bc) (hq : 0<q) (hCap : q≤qbar) (hDen : Bc.den∣q) :
    (run bits model W k Qv a c hc weights Bc Br shared hs).1.2=true := by
  rw [data]
  exact GeneralPaperSourceRowsContract.source_checks bits model W k Qv q qbar a hm hQv weights hw Bc Br hB hq hCap hDen

theorem bit_profile_mono (actual majorant : RationalCostModel) (h : ∀ w,actual.rat w≤majorant.rat w)
    (W T m t : ℕ) (a : Alphabet) :
    GeneralPaperSourceRowsExecution.bitProfile actual W T m t a≤
      GeneralPaperSourceRowsExecution.bitProfile majorant W T m t a := by
  unfold GeneralPaperSourceRowsExecution.bitProfile rowBitProfile GeneralPaperClosedBidExecution.bitProfile
    GeneralPaperRowBudgetExecution.bitProfile
  gcongr <;> apply h

def bitProfile (C d W m k Qv t : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperFastSourceMajorant.profile C d W m k Qv a (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+
    GeneralPaperSourceRowsExecution.bitProfile (GeneralPaperFastRationalMajorant.model C d) W
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m t a+
    64*arrayWord W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs

def arithmeticProfile (m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperGeometricSourcePrice.arithmeticProfile m k Qv a (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+
    GeneralPaperSourceRowsExecution.arithmeticProfile (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m a+64

theorem bit_work {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W k Qv t : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m)
    (hs : shared=prepare a k Qv weights Bc Br) (hw : ∑ j,weights.read j=Qv)
    (hB : RationalHeight Bc t)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    (run true actual W k Qv a c hc weights Bc Br shared hs).2≤bitProfile C d W m k Qv t a := by
  subst shared
  have ht := GeneralPaperSourceRowsContract.native_table true actual W k Qv a c hc weights Bc Br
    _ rfl (produced_size true actual W k Qv a c hc weights Bc Br _ rfl)
  have hSource := GeneralPaperFastSourceMajorant.native_work hg W k Qv a c hc weights Bc Br hw
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs le_rfl hbc hbr
  have hRows := GeneralPaperSourceRowsContract.source_bit_work actual W k Qv t a weights Bc Br hB
  have hMono := bit_profile_mono actual _ (GeneralPaperFastRationalMajorant.dominates hg) W
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m t a
  unfold run bitProfile
  dsimp only
  rw [ht]
  dsimp only [prepare,address,ite_true]
  exact Nat.add_le_add_right (Nat.add_le_add hSource (hRows.trans hMono)) _

theorem arithmetic_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m)
    (hs : shared=prepare a k Qv weights Bc Br) (hw : ∑ j,weights.read j=Qv) :
    (run false model 1 k Qv a c hc weights Bc Br shared hs).2≤arithmeticProfile m k Qv a := by
  subst shared
  have ht := GeneralPaperSourceRowsContract.native_table false model 1 k Qv a c hc weights Bc Br
    _ rfl (produced_size false model 1 k Qv a c hc weights Bc Br _ rfl)
  have hSource := (GeneralPaperGeometricSourcePrice.work model 1 k Qv a c hc weights Bc Br hw
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs le_rfl).2
  have hRows := GeneralPaperSourceRowsContract.source_arithmetic_work model k Qv a weights Bc Br
  unfold run arithmeticProfile
  dsimp only
  rw [ht]
  simp only [prepare,address,Bool.false_eq_true,ite_false,Nat.mul_one]
  exact Nat.add_le_add_right (Nat.add_le_add hSource hRows) _

end Blotto.GeneralPaperSourceRowsDriver
