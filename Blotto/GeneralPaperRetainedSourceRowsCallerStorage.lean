import Blotto.GeneralPaperSourceInputEnvelopeStorage

/-! Actual retained source-row caller. Materialized cache, shared record,
full geometric-source lifetime and complete row postprocessing coexist
with full returned rational rows and literal caller counters. All observers
are erased; actual source/decoder runs and original whole-row IDs remain. -/
namespace Blotto.GeneralPaperRetainedSourceRowsCallerStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperEncodedScalarStorage
open GeneralPaperSummaryArrayExecution (arrayWord)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def metadataCap (W m k Qv P : ℕ) (a : Alphabet) : ℕ :=
  m+k+Qv+(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows+
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+P+
    64*arrayWord W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+1

noncomputable def window {m : ℕ} (actual : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let E := (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs
  let T := (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
  let shared := prepare a k Qv weights Bc Br
  let source := GeneralPaperGeometricSourceExecution.run true (fun w => w) actual W k Qv a c hc shared E
  let codes : FixedArrayTable T (FixedArrayTable m ℕ) :=
    ⟨source.1.2,GeneralPaperSourceRowsDriver.produced_size true actual W k Qv a c hc weights Bc Br shared rfl⟩
  let returned := GeneralPaperSourceRowsExecution.run true actual W a codes Bc
  let result := GeneralPaperSourceRowsDriver.run true actual W k Qv a c hc weights Bc Br shared rfl
  GeneralPaperMaterializedCacheStorage.powerFootprint W c+GeneralPaperEncodedSharedSource.footprint W shared+
    GeneralPaperSourceLifetimeStorage.window actual W k Qv a c hc weights Bc Br E+
    GeneralPaperSourceRowsStorage.window actual W a codes Bc+
    GeneralPaperEnclosingSourceOwners.rowsFoot W returned.1.1+
    fields W [m,k,Qv,T,E,source.2,returned.2,result.2,source.2+returned.2,64*arrayWord W E,
      GeneralPaperFinalStaticLoopStorage.bit returned.1.2]+128*W

noncomputable def profile (upper : RationalCostModel) (W m k Qv t P : ℕ) (a : Alphabet) : ℕ :=
  3*GeneralPaperSourceInputEnvelopeStorage.profile upper W m k Qv t a
    (GeneralPaperSourceInputEnvelopeStorage.inputCap W m Qv t) (1+2*t) (1+2*t)+
    GeneralPaperSourceRowsStorage.profile upper W (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m t a+
    GeneralPaperEnclosingSourceOwners.rowsProfile W (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m (1+2*binaryWordWidth a.C)+
    11*(natBits (metadataCap W m k Qv P a)+W)+160*W

theorem retained_result {m : ℕ} (actual : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    GeneralPaperRetainedSourceRows.run true actual W k Qv a c hc weights Bc Br shared hs hT=
      GeneralPaperSourceRowsDriver.run true actual W k Qv a c hc weights Bc Br shared hs :=
  GeneralPaperRetainedSourceRows.data true actual W k Qv a c hc weights Bc Br shared hs hT

theorem bounded {m : ℕ} (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (W k Qv t P : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (hs : ∑ j,weights.read j=Qv) (Bc Br : ℚ)
    (hBc : RationalHeight Bc t) (hBr : RationalHeight Br t)
    (hP : (GeneralPaperSourceRowsDriver.run true actual W k Qv a c hc weights Bc Br (prepare a k Qv weights Bc Br) rfl).2≤P) :
    window actual W k Qv a c hc weights Bc Br≤profile upper W m k Qv t P a := by
  let E := (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs
  let T := (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
  let shared := prepare a k Qv weights Bc Br
  let source := GeneralPaperGeometricSourceExecution.run true (fun w => w) actual W k Qv a c hc shared E
  let codes : FixedArrayTable T (FixedArrayTable m ℕ) :=
    ⟨source.1.2,GeneralPaperSourceRowsDriver.produced_size true actual W k Qv a c hc weights Bc Br shared rfl⟩
  let returned := GeneralPaperSourceRowsExecution.run true actual W a codes Bc
  let result := GeneralPaperSourceRowsDriver.run true actual W k Qv a c hc weights Bc Br shared rfl
  let F := GeneralPaperSourceInputEnvelopeStorage.inputCap W m Qv t
  let B := GeneralPaperSourceInputEnvelopeStorage.profile upper W m k Qv t a F (1+2*t) (1+2*t)
  have hF := GeneralPaperSourceInputEnvelopeStorage.input_bound W Qv t weights hs Bc Br hBc hBr
  have hPrepared := GeneralPaperSourceInputEnvelopeStorage.prepared_bound upper W k Qv t F (1+2*t) (1+2*t)
    a weights Bc Br hF (rationalWordWidth_of_height hBc) (rationalWordWidth_of_height hBr)
  change GeneralPaperPreparedReferenceCapacity.profile upper W k Qv 0 t t a weights Bc Br≤B at hPrepared
  have hCache : GeneralPaperMaterializedCacheStorage.powerFootprint W c≤B := by
    rw [hc]
    exact (GeneralPaperMaterializedCacheStorage.power_native W m a.lambda k Qv).trans
      ((GeneralPaperSourceInputEnvelopeStorage.power_profile upper W k Qv t a weights Bc Br).trans hPrepared)
  have hShared : GeneralPaperEncodedSharedSource.footprint W shared≤B :=
    (GeneralPaperEncodedSharedSource.native W k Qv a weights Bc Br).trans
      ((GeneralPaperSourceInputEnvelopeStorage.shared_profile upper W k Qv t a weights Bc Br).trans hPrepared)
  have hSource := (GeneralPaperSourceLifetimeStorage.bounded actual W k Qv a c hc weights Bc Br hs E le_rfl).trans
    (GeneralPaperSourceInputEnvelopeStorage.lifetime_bound actual upper h W k Qv t F (1+2*t) (1+2*t) a weights Bc Br hF
      (rationalWordWidth_of_height hBc) (rationalWordWidth_of_height hBr))
  change GeneralPaperSourceLifetimeStorage.window actual W k Qv a c hc weights Bc Br E≤B at hSource
  have hCode : ∀ i j,(codes.read i).read j≤8*a.C := by
    have ht := GeneralPaperSourceRowsContract.native_table true actual W k Qv a c hc weights Bc Br source.1.2 rfl
      (GeneralPaperSourceRowsDriver.produced_size true actual W k Qv a c hc weights Bc Br shared rfl)
    change codes=GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br at ht
    rw [ht]
    exact GeneralPaperSourceRowsContract.code_bound a k Qv weights Bc Br
  have hPost := (GeneralPaperSourceRowsStorage.bounded actual W t a codes Bc hBc hCode).trans
    (GeneralPaperSourceRowsStorageRates.storage_mono actual upper h W T m t a)
  have hRows := GeneralPaperEnclosingSourceOwners.rows_bound W (1+2*binaryWordWidth a.C) returned.1.1 (by
    intro i j
    change rationalWordWidth (((GeneralPaperSourceRowsExecution.run true actual W a codes Bc).1.1.read i).read j)≤_
    rw [GeneralPaperSourceRowsExecution.data true actual W 0,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.decoded_height m 0 a _))
  change result.2≤P at hP
  have hShape : result.2=source.2+returned.2+64*arrayWord W E := rfl
  have hBit := GeneralPaperFinalStaticLoopStorage.bit_bound returned.1.2
  have hf := fields_bound W (natBits (metadataCap W m k Qv P a))
    [m,k,Qv,T,E,source.2,returned.2,result.2,source.2+returned.2,64*arrayWord W E,
      GeneralPaperFinalStaticLoopStorage.bit returned.1.2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; dsimp only [T,E] at *; omega)
  change fields W _≤11*(natBits (metadataCap W m k Qv P a)+W)+32*W at hf
  change GeneralPaperMaterializedCacheStorage.powerFootprint W c+GeneralPaperEncodedSharedSource.footprint W shared+
    GeneralPaperSourceLifetimeStorage.window actual W k Qv a c hc weights Bc Br E+
    GeneralPaperSourceRowsStorage.window actual W a codes Bc+GeneralPaperEnclosingSourceOwners.rowsFoot W returned.1.1+
    fields W [m,k,Qv,T,E,source.2,returned.2,result.2,source.2+returned.2,64*arrayWord W E,
      GeneralPaperFinalStaticLoopStorage.bit returned.1.2]+128*W≤_
  unfold profile
  change _≤3*B+GeneralPaperSourceRowsStorage.profile upper W T m t a+
    GeneralPaperEnclosingSourceOwners.rowsProfile W T m (1+2*binaryWordWidth a.C)+
    11*(natBits (metadataCap W m k Qv P a)+W)+160*W
  omega

end Blotto.GeneralPaperRetainedSourceRowsCallerStorage
