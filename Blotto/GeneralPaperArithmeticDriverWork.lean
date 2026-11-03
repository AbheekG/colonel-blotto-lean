import Blotto.GeneralPaperArithmeticCompilerWork

/-! Once-only full arithmetic driver work, including native preparation,
both retained sources, quantization, values, selected compiler and parents.
Canonical data equalities discharge all compiler premises. -/
namespace Blotto.GeneralPaperArithmeticDriverWork
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint GeneralPaperCatalogueShared
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def preparedPrice (m k Qv : ℕ) : ℕ :=
  (79*m+237)+2*GeneralPaperArithmeticUnitSourceWork.sourcePrice m k Qv+GeneralPaperArithmeticCompilerWork.price m k+128
def cachedPrice (m k Qv : ℕ) : ℕ := 256+256+preparedPrice m k Qv+128
def price (m k Qv : ℕ) : ℕ := GeneralPaperArithmeticPairPreparation.profile m k Qv+cachedPrice m k Qv+64

theorem prepared_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (rich poor : Shared m)
    (hRich : rich=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights 1 (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value)
    (hPoor : poor=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value 1)
    (hRT : rich.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)
    (hPT : poor.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (GeneralPaperPreparedSourceCompilerPair.run model k Qv hQv weights hp hw (GeneralPaperPrecallCachePrice.specification m k) (grid_positive m k)
      (alphabet m k) c hc (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      rich poor hRich hPoor hRT hPT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).2≤preparedPrice m k Qv := by
  let values := GeneralPaperRetainedFieldValues.run false model 1 Qv hQv weights hp hw
  let rc := GeneralPaperRetainedSourceColumns.run model k Qv (alphabet m k) c hc weights 1
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value rich hRich hRT
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  let pc := GeneralPaperRetainedSourceColumns.run model k Qv (alphabet m k) c hc weights
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value 1 poor hPoor hPT
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  have hrData := GeneralPaperRetainedSourceColumns.actual_data model k Qv b false c hc weights rich hRich hRT
  have hpData := GeneralPaperRetainedSourceColumns.actual_data model k Qv b true c hc weights poor hPoor hPT
  have hvData := GeneralPaperRetainedFieldValues.selector_data false model 1 Qv hQv weights hp hw
  have hv := GeneralPaperRetainedFieldValues.arithmetic_work model Qv hQv weights hp hw
  have hr := GeneralPaperArithmeticUnitSourceWork.source_work model k Qv weights hw b hb false c hc rich hRich hRT
  have hp' := GeneralPaperArithmeticUnitSourceWork.source_work model k Qv weights hw b hb true c hc poor hPoor hPT
  have hCompiler := GeneralPaperArithmeticCompilerWork.pair_work model k Qv hm hQv weights hp hw b hb
    ⟨rc.1.1,pc.1.1⟩ values.1 hrData hpData hvData
  dsimp only [GeneralPaperPreparedSourceCompilerPair.run,GeneralPaperPrecallCachePrice.specification]
  change values.2≤79*m+237 at hv
  change rc.2≤GeneralPaperArithmeticUnitSourceWork.sourcePrice m k Qv at hr
  change pc.2≤GeneralPaperArithmeticUnitSourceWork.sourcePrice m k Qv at hp'
  dsimp only [values,rc,pc] at hv hr hp' hCompiler
  split
  · dsimp only
    have hTotal := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hv hr) hp') hCompiler) 128
    exact hTotal.trans_eq (by unfold preparedPrice;ring)
  · dsimp only
    unfold preparedPrice
    omega

theorem cached_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (x : GeneralPaperCachedSourcePair.Input m k Qv b) :
    (GeneralPaperCachedSourcePair.run model k Qv hQv weights hp hw b x).2≤cachedPrice m k Qv := by
  obtain ⟨control,a,grid,classified,hControl,hA,hGrid,hClass⟩ := x
  subst control
  subst a
  subst grid
  subst classified
  let g := GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv
  let rho := (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
  let rich := GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k (alphabet m k) g weights 1 rho
  let poor := GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k (alphabet m k) g weights rho 1
  have hrData : rich.1=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights 1 rho :=
    GeneralPaperCachedSharedPreparation.data (fun _ => 1) 1 k Qv (alphabet m k) g rfl weights 1 rho
  have hpData : poor.1=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights rho 1 :=
    GeneralPaperCachedSharedPreparation.data (fun _ => 1) 1 k Qv (alphabet m k) g rfl weights rho 1
  have hRT : rich.1.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hrData];rfl
  have hPT : poor.1.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hpData];rfl
  have hPrepared := prepared_work model k Qv hm hQv weights hp hw b hb g.source rfl rich.1 poor.1 hrData hpData hRT hPT
  have hr := GeneralPaperCachedSharedPreparation.arithmetic_work k (alphabet m k) g weights 1 rho
  have hp' := GeneralPaperCachedSharedPreparation.arithmetic_work k (alphabet m k) g weights rho 1
  dsimp only [GeneralPaperCachedSourcePair.run]
  dsimp only [rich,poor,g,rho] at hPrepared hr hp'
  unfold cachedPrice
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hr hp') hPrepared) 128

theorem work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    (GeneralPaperArithmeticSourcePairDriver.run model k Qv hQv weights hp hw b).2≤price m k Qv := by
  have hPrep := GeneralPaperArithmeticPairPreparation.arithmetic_work m k Qv b hb
  have hCached := cached_work model k Qv hm hQv weights hp hw b hb (GeneralPaperArithmeticPairPreparation.run m k Qv b).1
  dsimp only [GeneralPaperArithmeticSourcePairDriver.run]
  unfold price
  omega

end Blotto.GeneralPaperArithmeticDriverWork
