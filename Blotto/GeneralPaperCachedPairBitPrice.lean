import Blotto.GeneralPaperPreparedPairBitPrice
import Blotto.GeneralPaperCachedBitSourcePair

/-! Complete cached-pair price including raw proxy decoding, both Shared
records and the prepared two-source/selected-compiler phase. All cached
control/data identities erase; the actual retained grid executes once. -/
namespace Blotto.GeneralPaperCachedPairBitPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperProxyParameters
open GeneralPaperCachedSourcePair
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def sharedProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  192*W+5*model.rat (GeneralPaperSharedSpanPrice.width (alphabet m k))+
    6*model.rat (GeneralPaperSharedWidthPrice.width
      (GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv).source.powers.format.fractionalBits k)

def profile (model : RationalCostModel) (C d W m k Qv p q : ℕ) : ℕ :=
  6*model.rat (1+2*binaryWordWidth (prepare m k).qbar)+2*sharedProfile model W m k Qv+
    GeneralPaperPreparedPairBitPrice.profile model C d W m k Qv p q+160*W

theorem sum_bound (v r p c P B D W : ℕ) (hv : v≤6*P+32*W) (hr : r≤B) (hp : p≤B) (hc : c≤D) :
    v+r+p+c+128*W≤6*P+2*B+D+160*W := by omega

theorem actual_work {m : ℕ} {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (x : Input m k Qv b)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) (hColumnsIndex : binaryWordWidth (m+(prepare m k).K+1)≤W)
    (hRowsIndex : binaryWordWidth (2*(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(prepare m k).K+m+1)≤W) :
    (GeneralPaperCachedBitSourcePair.run model W k Qv hQv weights hp hw b x).2≤
      profile model C d W m k Qv (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
        (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den := by
  obtain ⟨control,a,grid,classified,hControl,hA,hGrid,hClass⟩ := x
  subst control;subst a;subst grid;subst classified
  let g := GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let rho := f.value
  let rich := GeneralPaperCachedSharedPreparation.fromCache model.rat W k (alphabet m k) g weights 1 rho
  let poor := GeneralPaperCachedSharedPreparation.fromCache model.rat W k (alphabet m k) g weights rho 1
  have hr : rich.1=prepare (alphabet m k) k Qv weights 1 rho :=
    GeneralPaperCachedSharedPreparation.data model.rat W k Qv (alphabet m k) g rfl weights 1 rho
  have hp' : poor.1=prepare (alphabet m k) k Qv weights rho 1 :=
    GeneralPaperCachedSharedPreparation.data model.rat W k Qv (alphabet m k) g rfl weights rho 1
  have hRT : rich.1.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hr];rfl
  have hPT : poor.1.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hp'];rfl
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hDecode := GeneralPaperCachedBitSourcePair.decode_work model W (prepare m k).qbar f (hf.2.1.le.trans hf.2.2) hf.2.2
  have hRich := GeneralPaperCachedSharedPreparation.work model.rat model.monotone W k (alphabet m k) g weights 1 rho
  have hPoor := GeneralPaperCachedSharedPreparation.work model.rat model.monotone W k (alphabet m k) g weights rho 1
  have hPair := GeneralPaperPreparedPairBitPrice.actual_work hg W k Qv hm hQv weights hp hw b hb g.source rfl
    rich.1 poor.1 hr hp' hRT hPT hW hDim hK hM hIndex hBatch hFinal hColumnsIndex hRowsIndex
  dsimp only [GeneralPaperCachedBitSourcePair.run]
  simp only [GeneralPaperCachedBitSourcePair.decode_data]
  exact sum_bound _ _ _ _ _ _ _ W hDecode hRich hPoor hPair

end Blotto.GeneralPaperCachedPairBitPrice
