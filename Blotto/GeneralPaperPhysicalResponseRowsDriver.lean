import Blotto.GeneralPaperPhysicalResponseSourceRates

/-! Run the checked source once, decode its full candidate table once, and
combine response and output budget flags. The retained tree cache and
shared parameters are borrowed; table size proofs erase. -/
namespace Blotto.GeneralPaperPhysicalResponseRowsDriver
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperSourceRowsExecution
open GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

theorem produced_size {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br) :
    (GeneralPaperPhysicalResponseSourceCache.run bits model W k Qv qbar a c hc shared
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).1.1.2.size=
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows := by
  rw [hs]
  exact (GeneralPaperPhysicalResponseSourceCache.size bits model W k Qv qbar a c hc weights Bc Br
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs le_rfl).trans
      (GeneralPaperTrajectoryParameters.rows_product a.lambda k).symm

theorem native_table {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br) :
    (⟨(GeneralPaperPhysicalResponseSourceCache.run bits model W k Qv qbar a c hc shared
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).1.1.2,
      produced_size bits model W k Qv qbar a c hc weights Bc Br shared hs⟩ : FixedArrayTable _ _)=
      GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br := by
  subst shared
  exact GeneralPaperSourceRowsContract.native_table bits model W k Qv a c hc weights Bc Br _
    (congrArg Prod.snd (GeneralPaperPhysicalResponseSourceCache.base_data bits model W k Qv qbar a c hc _ _)) _

def run {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br) :
    (FixedArrayTable (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows (FixedArrayTable m ℚ) × Bool) × ℕ :=
  let source := GeneralPaperPhysicalResponseSourceCache.run bits model W k Qv qbar a c hc shared
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs
  let codes : FixedArrayTable (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows (FixedArrayTable m ℕ) :=
    ⟨source.1.1.2,produced_size bits model W k Qv qbar a c hc weights Bc Br shared hs⟩
  let returned := GeneralPaperSourceRowsExecution.run bits model W a codes shared.Bc
  ((returned.1.1,source.1.2 && returned.1.2),source.2+returned.2+
    64*address bits W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+
    32*address bits W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)

theorem row_phase {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br) :
    (run bits model W k Qv qbar a c hc weights Bc Br shared hs).1=
      let returned := GeneralPaperSourceRowsExecution.run bits model W a
        (GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br) Bc
      (returned.1.1,(GeneralPaperPhysicalResponseSourceCache.run bits model W k Qv qbar a c hc shared
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).1.2 && returned.1.2) := by
  subst shared
  unfold run
  dsimp only
  rw [native_table bits model W k Qv qbar a c hc weights Bc Br _ rfl]
  rfl

theorem rational_data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br) :
    (run bits model W k Qv qbar a c hc weights Bc Br shared hs).1.1=
      GeneralPaperCatalogueRationalTrajectory.rows a k Qv qbar weights Bc Br := by
  rw [row_phase]
  exact GeneralPaperSourceRowsContract.source_data bits model W k Qv qbar a weights Bc Br

theorem checked {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv q qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hm : 0<m) (hQv : 0<Qv) (hw : ∑ j,weights.read j=Qv) (hBc : 0≤Bc) (hBr : 0≤Br)
    (hq : 0<q) (hCap : q≤qbar) (hDc : Bc.den∣q) (hDr : Br.den∣q) :
    (run bits model W k Qv qbar a c hc weights Bc Br shared hs).1.2=true := by
  subst shared
  rw [row_phase]
  dsimp only
  rw [GeneralPaperPhysicalResponseSourceCache.checked bits model W k Qv q qbar a c hc weights Bc Br
      _ hm hQv hq hCap hw hBr hDr le_rfl,
    GeneralPaperSourceRowsContract.source_checks bits model W k Qv q qbar a hm hQv weights hw Bc Br hBc hq hCap hDc]
  rfl

theorem models_data {m : ℕ} (model : RationalCostModel) (W k Qv q qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hm : 0<m) (hQv : 0<Qv) (hw : ∑ j,weights.read j=Qv) (hBc : 0≤Bc) (hBr : 0≤Br)
    (hq : 0<q) (hCap : q≤qbar) (hDc : Bc.den∣q) (hDr : Br.den∣q) :
    (run true model W k Qv qbar a c hc weights Bc Br shared hs).1=
      (run false model 1 k Qv qbar a c hc weights Bc Br shared hs).1 := by
  apply Prod.ext
  · exact (rational_data true model W k Qv qbar a c hc weights Bc Br shared hs).trans
      (rational_data false model 1 k Qv qbar a c hc weights Bc Br shared hs).symm
  · rw [checked true model W k Qv q qbar a c hc weights Bc Br shared hs hm hQv hw hBc hBr hq hCap hDc hDr,
      checked false model 1 k Qv q qbar a c hc weights Bc Br shared hs hm hQv hw hBc hBr hq hCap hDc hDr]

def bitProfile {m : ℕ} (C d W k Qv qbar t : ℕ) (a : Alphabet) (shared : Shared m) : ℕ :=
  GeneralPaperPhysicalResponseSourcePrice.bitProfile C d W k Qv qbar t a shared
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+
    GeneralPaperSourceRowsExecution.bitProfile (GeneralPaperFastRationalMajorant.model C d) W
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m t a+
    96*arrayWord W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs

def arithmeticProfile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (shared : Shared m) : ℕ :=
  GeneralPaperPhysicalResponseSourcePrice.arithmeticProfile k Qv a shared
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+
    GeneralPaperSourceRowsExecution.arithmeticProfile (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m a+96

theorem bit_work {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W k Qv qbar t : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hw : ∑ j,weights.read j=Qv) (hBc : RationalHeight Bc t) (hBr : RationalHeight Br t)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    (run true actual W k Qv qbar a c hc weights Bc Br shared hs).2≤bitProfile C d W k Qv qbar t a shared := by
  subst shared
  have hSource := GeneralPaperPhysicalResponseSourcePrice.bit_work hg W k Qv qbar t a c hc weights Bc Br hw
    _ le_rfl hBr hbc hbr
  have hRows := GeneralPaperSourceRowsContract.source_bit_work actual W k Qv t a weights Bc Br hBc
  have hMono := GeneralPaperSourceRowsDriver.bit_profile_mono actual _ (GeneralPaperFastRationalMajorant.dominates hg) W
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m t a
  have ht := native_table true actual W k Qv qbar a c hc weights Bc Br _ rfl
  unfold run bitProfile
  dsimp only
  rw [ht,show (prepare a k Qv weights Bc Br).Bc=Bc from rfl]
  dsimp only at hSource
  simp only [address,ite_true]
  nlinarith only [hSource,hRows,hMono]

theorem arithmetic_work {m : ℕ} (model : RationalCostModel) (k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hw : ∑ j,weights.read j=Qv) :
    (run false model 1 k Qv qbar a c hc weights Bc Br shared hs).2≤arithmeticProfile k Qv a shared := by
  subst shared
  have hSource := GeneralPaperPhysicalResponseSourcePrice.arithmetic_work model k Qv qbar a c hc weights Bc Br hw _ le_rfl
  have hRows := GeneralPaperSourceRowsContract.source_arithmetic_work model k Qv a weights Bc Br
  have ht := native_table false model 1 k Qv qbar a c hc weights Bc Br _ rfl
  unfold run arithmeticProfile
  dsimp only
  rw [ht,show (prepare a k Qv weights Bc Br).Bc=Bc from rfl]
  dsimp only at hSource
  simp only [address,Bool.false_eq_true,ite_false,Nat.mul_one]
  nlinarith only [hSource,hRows]

end Blotto.GeneralPaperPhysicalResponseRowsDriver
