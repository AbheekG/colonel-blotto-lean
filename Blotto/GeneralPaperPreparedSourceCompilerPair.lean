import Blotto.GeneralPaperRetainedSourceColumns

/-! Full arithmetic source-to-column-pair execution on retained prepared
objects. Both players' full sources execute once, each is quantized and
normalized once, and owned field values materialize once. Only the selected
defender runs the strict compiler. The caller supplies cached numeric T/K
and cache records; their native construction is the surrounding phase. -/
namespace Blotto.GeneralPaperPreparedSourceCompilerPair
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperOriginalDrawEquilibrium
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {m T K : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (control : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<control.proxy.Qg) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (rich poor : Shared m) (hRich : rich=prepare a k Qv weights 1 proxyValue) (hPoor : poor=prepare a k Qv weights proxyValue 1)
    (hRT : rich.trajectory.rows=T) (hPT : poor.trajectory.rows=T) (hT : 0<T) (hK : 0<K) (hDiv : K∣T) :
    Option (Columns T m K)×ℕ :=
  let values := GeneralPaperRetainedFieldValues.run false model 1 Qv hQv weights hp hw
  let rc := GeneralPaperRetainedSourceColumns.run model k Qv a c hc weights 1 proxyValue rich hRich hRT hT hK hDiv
  let pc := GeneralPaperRetainedSourceColumns.run model k Qv a c hc weights proxyValue 1 poor hPoor hPT hT hK hDiv
  if rc.1.2 && pc.1.2 then
    let compiled := GeneralPaperRetainedCompilerPair.run model control.score.depth control.proxy.S control.proxy.H control.proxy.Qg hQ hK
      classified proxyValue values.1 ⟨rc.1.1,pc.1.1⟩
    (compiled.1,values.2+rc.2+pc.2+compiled.2+128)
  else (none,values.2+rc.2+pc.2+64)

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (rich poor : Shared m)
    (hRich : rich=prepare (alphabet m k) k Qv weights 1 (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value)
    (hPoor : poor=prepare (alphabet m k) k Qv weights (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value 1)
    (hRT : rich.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)
    (hPT : poor.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (run model k Qv hQv weights hp hw (GeneralPaperPrecallCachePrice.specification m k) (grid_positive m k)
      (alphabet m k) c hc (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      rich poor hRich hPoor hRT hPT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1.map GeneralPaperPhysicalColumnPair.decode=
        GeneralPaperCheckedSourcePair.run k Qv hQv weights hp hw b := by
  have hr := GeneralPaperRetainedSourceColumns.actual_data model k Qv b false c hc weights rich hRich hRT
  have hp' := GeneralPaperRetainedSourceColumns.actual_data model k Qv b true c hc weights poor hPoor hPT
  have hrc := GeneralPaperRetainedSourceColumns.actual_checked model k Qv hm hQv b hb false c hc weights hw rich hRich hRT
  have hpc := GeneralPaperRetainedSourceColumns.actual_checked model k Qv hm hQv b hb true c hc weights hw poor hPoor hPT
  have hv := GeneralPaperRetainedFieldValues.selector_data false model 1 Qv hQv weights hp hw
  dsimp only [run]
  erw [hrc,hpc]
  exact GeneralPaperRetainedPairSource.data model k Qv hm hQv weights hp hw b hb _ _ hr hp' hv

end Blotto.GeneralPaperPreparedSourceCompilerPair
