import Blotto.GeneralPaperColumnPairReindex

/-! Prepared native arithmetic pair from returned classifier/control/grid
caches. A raw proxy fraction is decoded once and supplies both Shared
records. Cached row/label counts control all source/quantizer/compiler
loops; only erased return-size casts mention canonical parameters. -/
namespace Blotto.GeneralPaperCachedSourcePair
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperProxyParameters
open GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

structure Input (m k Qv : ℕ) (b : ℝ) where
  control : GeneralPaperPrecallCachePrice.Cache
  alphabet : Alphabet
  grid : GeneralPaperMaterializedGridCache.Cache
  classified : GeneralPaperProxyClassifier.Result
  control_data : control=GeneralPaperPrecallCachePrice.specification m k
  alphabet_data : alphabet=GeneralPaperProxyParameters.alphabet m k
  grid_data : grid=GeneralPaperMaterializedGridCache.specification m alphabet.lambda k Qv
  classified_data : classified=GeneralPaperProxyClassifier.classify m k b

theorem source_data {m k Qv : ℕ} {b : ℝ} (x : Input m k Qv b) :
    x.grid.source=GeneralPaperMaterializedPowerCache.specification m x.alphabet.lambda k Qv := by
  rw [x.grid_data]
  rfl

theorem rows_data {m k Qv : ℕ} {b : ℝ} (x : Input m k Qv b) :
    x.grid.source.controls.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare x.alphabet.lambda k).rows := by
  rw [source_data x]
  rfl

theorem canonical_rows {m k Qv : ℕ} {b : ℝ} (x : Input m k Qv b) :
    x.grid.source.controls.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows := by
  rw [rows_data x,x.alphabet_data]

theorem canonical_labels {m k Qv : ℕ} {b : ℝ} (x : Input m k Qv b) :
    x.control.proxy.K=(GeneralPaperProxyParameters.prepare m k).K := by
  rw [x.control_data]
  rfl

def run {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (x : Input m k Qv b) :
    Option (Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
      m (GeneralPaperProxyParameters.prepare m k).K)×ℕ :=
  let rho := x.classified.choice.proxy.value
  let rich := GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k x.alphabet x.grid weights 1 rho
  let poor := GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k x.alphabet x.grid weights rho 1
  let hRich := GeneralPaperCachedSharedPreparation.data (fun _ => 1) 1 k Qv x.alphabet x.grid x.grid_data weights 1 rho
  let hPoor := GeneralPaperCachedSharedPreparation.data (fun _ => 1) 1 k Qv x.alphabet x.grid x.grid_data weights rho 1
  let hRT : rich.1.trajectory.rows=x.grid.source.controls.trajectory.rows := by rw [hRich,rows_data x];rfl
  let hPT : poor.1.trajectory.rows=x.grid.source.controls.trajectory.rows := by rw [hPoor,rows_data x];rfl
  let hT : 0<x.grid.source.controls.trajectory.rows := by rw [rows_data x];exact GeneralPaperTrajectoryParameters.rows_positive x.alphabet.lambda k
  let hK : 0<x.control.proxy.K := by rw [canonical_labels x];exact GeneralPaperScoreScaleParameters.labels_positive m k
  let hDiv : x.control.proxy.K∣x.grid.source.controls.trajectory.rows := by
    rw [canonical_labels x,canonical_rows x]
    exact GeneralPaperTrajectoryParameters.labels_divide_rows m (GeneralPaperProxyParameters.alphabet m k).lambda k
  let hQ : 0<x.control.proxy.Qg := by rw [x.control_data];exact GeneralPaperProxyParameters.grid_positive m k
  let compiled := GeneralPaperPreparedSourceCompilerPair.run model k Qv hQv weights hp hw x.control hQ x.alphabet
    x.grid.source (source_data x) x.classified rho rich.1 poor.1 hRich hPoor hRT hPT hT hK hDiv
  (compiled.1.map (GeneralPaperColumnPairReindex.run (canonical_rows x) (canonical_labels x)),
    rich.2+poor.2+compiled.2+128)

end Blotto.GeneralPaperCachedSourcePair
