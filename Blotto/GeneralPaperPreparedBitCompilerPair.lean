import Blotto.GeneralPaperRetainedSourceColumnBits
import Blotto.GeneralPaperPreparedSourceCompilerPair

/-! The prepared pair now uses bit prices through both geometric sources,
full row checks, quantizers, normalizers, stored values and the selected
strict compiler. Both sources share the retained grid/controls. -/
namespace Blotto.GeneralPaperPreparedBitCompilerPair
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperOriginalDrawEquilibrium
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 8192

def run {m T K : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (control : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<control.proxy.Qg) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (rich poor : Shared m) (hRich : rich=prepare a k Qv weights 1 proxyValue) (hPoor : poor=prepare a k Qv weights proxyValue 1)
    (hRT : rich.trajectory.rows=T) (hPT : poor.trajectory.rows=T) (hT : 0<T) (hK : 0<K) (hDiv : K∣T) :
    Option (Columns T m K)×ℕ :=
  let values := GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hw
  let rc := GeneralPaperRetainedSourceColumnBits.run model W k Qv a c hc weights 1 proxyValue rich hRich hRT hT hK hDiv
  let pc := GeneralPaperRetainedSourceColumnBits.run model W k Qv a c hc weights proxyValue 1 poor hPoor hPT hT hK hDiv
  if rc.1.2 && pc.1.2 then
    let compiled := GeneralPaperRetainedCompilerPairBits.run model W control.score.depth control.proxy.S control.proxy.H control.proxy.Qg hQ hK
      classified proxyValue values.1 ⟨rc.1.1,pc.1.1⟩
    (compiled.1,values.2+rc.2+pc.2+compiled.2+128*W)
  else (none,values.2+rc.2+pc.2+64*W)

theorem run_data {m T K : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (control : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<control.proxy.Qg) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (rich poor : Shared m) (hRich : rich=prepare a k Qv weights 1 proxyValue) (hPoor : poor=prepare a k Qv weights proxyValue 1)
    (hRT : rich.trajectory.rows=T) (hPT : poor.trajectory.rows=T) (hT : 0<T) (hK : 0<K) (hDiv : K∣T) :
    let values := GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hw
    let rc := GeneralPaperRetainedSourceColumnBits.run model W k Qv a c hc weights 1 proxyValue rich hRich hRT hT hK hDiv
    let pc := GeneralPaperRetainedSourceColumnBits.run model W k Qv a c hc weights proxyValue 1 poor hPoor hPT hT hK hDiv
    (run model W k Qv hQv weights hp hw control hQ a c hc classified proxyValue rich poor hRich hPoor hRT hPT hT hK hDiv).1=
      if rc.1.2 && pc.1.2 then
        (GeneralPaperRetainedCompilerPairBits.run model W control.score.depth control.proxy.S control.proxy.H control.proxy.Qg hQ hK
          classified proxyValue values.1 ⟨rc.1.1,pc.1.1⟩).1 else none := by
  dsimp only [run]
  split_ifs <;> rfl

theorem old_data {m T K : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (control : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<control.proxy.Qg) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (rich poor : Shared m) (hRich : rich=prepare a k Qv weights 1 proxyValue) (hPoor : poor=prepare a k Qv weights proxyValue 1)
    (hRT : rich.trajectory.rows=T) (hPT : poor.trajectory.rows=T) (hT : 0<T) (hK : 0<K) (hDiv : K∣T) :
    let values := GeneralPaperRetainedFieldValues.run false model 1 Qv hQv weights hp hw
    let rc := GeneralPaperRetainedSourceColumns.run model k Qv a c hc weights 1 proxyValue rich hRich hRT hT hK hDiv
    let pc := GeneralPaperRetainedSourceColumns.run model k Qv a c hc weights proxyValue 1 poor hPoor hPT hT hK hDiv
    (GeneralPaperPreparedSourceCompilerPair.run model k Qv hQv weights hp hw control hQ a c hc classified proxyValue rich poor hRich hPoor hRT hPT hT hK hDiv).1=
      if rc.1.2 && pc.1.2 then
        (GeneralPaperRetainedCompilerPair.run model control.score.depth control.proxy.S control.proxy.H control.proxy.Qg hQ hK
          classified proxyValue values.1 ⟨rc.1.1,pc.1.1⟩).1 else none := by
  dsimp only [GeneralPaperPreparedSourceCompilerPair.run]
  split_ifs <;> rfl

theorem data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (rich poor : Shared m)
    (hRich : rich=prepare (alphabet m k) k Qv weights 1 (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value)
    (hPoor : poor=prepare (alphabet m k) k Qv weights (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value 1)
    (hRT : rich.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)
    (hPT : poor.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (run model W k Qv hQv weights hp hw (GeneralPaperPrecallCachePrice.specification m k) (grid_positive m k)
      (alphabet m k) c hc (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      rich poor hRich hPoor hRT hPT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1=
      (GeneralPaperPreparedSourceCompilerPair.run model k Qv hQv weights hp hw (GeneralPaperPrecallCachePrice.specification m k) (grid_positive m k)
        (alphabet m k) c hc (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
        rich poor hRich hPoor hRT hPT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
        (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1 := by
  have hr := GeneralPaperRetainedSourceColumnBits.actual_models model W k Qv hm hQv b hb false c hc weights hw rich hRich hRT
  have hp' := GeneralPaperRetainedSourceColumnBits.actual_models model W k Qv hm hQv b hb true c hc weights hw poor hPoor hPT
  have hv := GeneralPaperRetainedBitData.values model W Qv hQv weights hp hw
  let values := GeneralPaperRetainedFieldValues.run false model 1 Qv hQv weights hp hw
  let rc := GeneralPaperRetainedSourceColumns.run model k Qv (alphabet m k) c hc weights 1
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value rich hRich hRT
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  let pc := GeneralPaperRetainedSourceColumns.run model k Qv (alphabet m k) c hc weights
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value 1 poor hPoor hPT
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  let brc := GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k) c hc weights 1
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value rich hRich hRT
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  let bpc := GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k) c hc weights
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value 1 poor hPoor hPT
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  let finish := fun (vv : GeneralPaperRetainedFieldValues.Values m)
      (rr pp : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K)×Bool) =>
    if rr.2 && pp.2 then
      (GeneralPaperRetainedCompilerPairBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth
        (prepare m k).S (prepare m k).H (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value vv ⟨rr.1,pp.1⟩).1
    else none
  have hFirst := congrArg₂ (fun vv rr => finish vv rr bpc.1) hv hr
  have hSecond := congrArg (fun pp => finish values.1 rc.1 pp) hp'
  have hFinish (vv : GeneralPaperRetainedFieldValues.Values m)
      (rr pp : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
        (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K)×Bool) :
      finish vv rr pp=if rr.2 && pp.2 then
        (GeneralPaperRetainedCompilerPair.run model (GeneralPaperScoreScaleParameters.prepare m k).depth
          (prepare m k).S (prepare m k).H (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
          (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value vv ⟨rr.1,pp.1⟩).1 else none := by
    dsimp only [finish]
    split_ifs
    · exact GeneralPaperRetainedCompilerPairBits.data model W k hm b hb vv ⟨rr.1,pp.1⟩
    · rfl
  erw [run_data,old_data]
  exact (hFirst.trans hSecond).trans (hFinish values.1 rc.1 pc.1)

end Blotto.GeneralPaperPreparedBitCompilerPair
