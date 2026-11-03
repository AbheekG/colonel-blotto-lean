import Blotto.GeneralPaperSourceCompilerPairBitPrice
import Blotto.GeneralPaperPreparedBitCompilerPair

/-! Complete local bit-price sum for the prepared physical pair: owned
values, both full geometric sources/row checks/quantizers/normalizers, and
the sole selected strict compiler. Budget heights are derived from the
constructed proxy, independently of the original input budget height. -/
namespace Blotto.GeneralPaperPreparedPairBitPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperOriginalDrawEquilibrium
open GeneralPaperProxyParameters GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem run_work {m T K : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (control : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<control.proxy.Qg) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (rich poor : Shared m) (hRich : rich=prepare a k Qv weights 1 proxyValue) (hPoor : poor=prepare a k Qv weights proxyValue 1)
    (hRT : rich.trajectory.rows=T) (hPT : poor.trajectory.rows=T) (hT : 0<T) (hK : 0<K) (hDiv : K∣T) :
    let values := GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hw
    let rc := GeneralPaperRetainedSourceColumnBits.run model W k Qv a c hc weights 1 proxyValue rich hRich hRT hT hK hDiv
    let pc := GeneralPaperRetainedSourceColumnBits.run model W k Qv a c hc weights proxyValue 1 poor hPoor hPT hT hK hDiv
    (GeneralPaperPreparedBitCompilerPair.run model W k Qv hQv weights hp hw control hQ a c hc classified proxyValue
      rich poor hRich hPoor hRT hPT hT hK hDiv).2≤
      values.2+rc.2+pc.2+
      (GeneralPaperRetainedCompilerPairBits.run model W control.score.depth control.proxy.S control.proxy.H control.proxy.Qg hQ hK
        classified proxyValue values.1 ⟨rc.1.1,pc.1.1⟩).2+128*W := by
  dsimp only [GeneralPaperPreparedBitCompilerPair.run]
  split_ifs <;> omega

def valueProfile (model : RationalCostModel) (W m Qv : ℕ) : ℕ :=
  m*(3*model.rat (GeneralPaperReducedValueArrayPrice.width Qv 1)+32*arrayWord W m)+
    44*(m+1)*arrayWord W m+model.rat (GeneralPaperReducedValueArrayPrice.width Qv 1)+192*arrayWord W m

def sourceProfile (model : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  let a := alphabet m k
  let T := (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
  GeneralPaperSourceRowsDriver.bitProfile C d W m k Qv (a.lambda+1) a+
  GeneralPaperNativeUnitSourceJoin.profile model.rat W (a.lambda+1) (binaryWordWidth a.C) T m (prepare m k).K
    (GeneralPaperNativeDivisibleColumns.blocks model.rat W T (prepare m k).K (GeneralPaperScoreScaleParameters.labels_positive m k)).1.val+64*W

def profile (model : RationalCostModel) (C d W m k Qv p q : ℕ) : ℕ :=
  valueProfile model W m Qv+2*sourceProfile model C d W m k Qv+
    GeneralPaperSourceCompilerPairBitPrice.profile model W m k Qv p q+128*W

theorem sum_bound (v r p c A B D W : ℕ) (hv : v≤A) (hr : r≤B) (hp : p≤B) (hc : c≤D) :
    v+r+p+c+128*W≤A+2*B+D+128*W := by omega

theorem actual_work {m : ℕ} {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (rich poor : Shared m)
    (hRich : rich=prepare (alphabet m k) k Qv weights 1 (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value)
    (hPoor : poor=prepare (alphabet m k) k Qv weights (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value 1)
    (hRT : rich.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)
    (hPT : poor.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) (hColumnsIndex : binaryWordWidth (m+(prepare m k).K+1)≤W)
    (hRowsIndex : binaryWordWidth (2*(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(prepare m k).K+m+1)≤W) :
    let classified := GeneralPaperProxyClassifier.classify m k b
    (GeneralPaperPreparedBitCompilerPair.run model W k Qv hQv weights hp hw (GeneralPaperPrecallCachePrice.specification m k) (grid_positive m k)
      (alphabet m k) c hc classified classified.choice.proxy.value rich poor hRich hPoor hRT hPT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).2≤
        profile model C d W m k Qv classified.choice.proxy.num classified.choice.proxy.den := by
  dsimp only
  let classified := GeneralPaperProxyClassifier.classify m k b
  let values := GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hw
  let rc := GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k) c hc weights 1 classified.choice.proxy.value
    rich hRich hRT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  let pc := GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k) c hc weights classified.choice.proxy.value 1
    poor hPoor hPT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  have hValue := GeneralPaperRetainedFieldValues.bit_work model W Qv hQv weights hp hw
  have hValueData := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hw
  have hRichPrice := GeneralPaperRetainedSourceColumnBits.work hg W k Qv ((alphabet m k).lambda+1) (alphabet m k) c hc weights hw
    1 classified.choice.proxy.value rich hRich hRT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperSourceBudgetWidths.own_height m k b hb false)
    ((GeneralPaperSourceBudgetWidths.own_word m k b hb false).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0))
    ((GeneralPaperSourceBudgetWidths.opposing_word m k b hb false).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0)) hW hRowsIndex
  have hPoorPrice := GeneralPaperRetainedSourceColumnBits.work hg W k Qv ((alphabet m k).lambda+1) (alphabet m k) c hc weights hw
    classified.choice.proxy.value 1 poor hPoor hPT (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperSourceBudgetWidths.own_height m k b hb true)
    ((GeneralPaperSourceBudgetWidths.own_word m k b hb true).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0))
    ((GeneralPaperSourceBudgetWidths.opposing_word m k b hb true).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0)) hW hRowsIndex
  have hRichData : GeneralPaperRowQuantizer.dictionary rc.1.1=GeneralPaperSourceUnchangedDictionary.run k Qv weights b false :=
    GeneralPaperRetainedSourceColumnBits.data model W k Qv (prepare m k).qbar (alphabet m k) c hc weights 1 classified.choice.proxy.value
      rich hRich hRT _ _ _
  have hPoorData : GeneralPaperRowQuantizer.dictionary pc.1.1=GeneralPaperSourceUnchangedDictionary.run k Qv weights b true :=
    GeneralPaperRetainedSourceColumnBits.data model W k Qv (prepare m k).qbar (alphabet m k) c hc weights classified.choice.proxy.value 1
      poor hPoor hPT _ _ _
  have hCompiler := GeneralPaperSourceCompilerPairBitPrice.actual_work model W k Qv hm hQv weights hp hw b hb ⟨rc.1.1,pc.1.1⟩ values.1
    hRichData hPoorData hValueData hW hDim hK hM hIndex hBatch hFinal hColumnsIndex
  have hRun := run_work model W k Qv hQv weights hp hw (GeneralPaperPrecallCachePrice.specification m k) (grid_positive m k)
    (alphabet m k) c hc classified classified.choice.proxy.value rich poor hRich hPoor hRT hPT
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
  exact hRun.trans (sum_bound _ _ _ _ _ _ _ W hValue hRichPrice hPoorPrice hCompiler)

end Blotto.GeneralPaperPreparedPairBitPrice
