import Blotto.GeneralPaperPreparedBitCompilerPair
import Blotto.GeneralPaperCachedSourcePairLaw

/-! Once-only bit execution from the returned classifier/control/grid
cache. The retained raw proxy is decoded once with its casts/division
priced, and the two Shared records retain the same grid by reference. -/
namespace Blotto.GeneralPaperCachedBitSourcePair
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperProxyParameters
open GeneralPaperCachedSourcePair GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def decode (model : RationalCostModel) (W : ℕ) (f : Farey.Fraction) : ℚ×ℕ :=
  let numerator : ℚ := f.num
  let denominator : ℚ := f.den
  (numerator/denominator,model.rat (1+binaryWordWidth f.num)+model.rat (1+binaryWordWidth f.den)+
    model.rat (rationalWordWidth numerator)+model.rat (rationalWordWidth denominator)+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) numerator denominator+32*W)

theorem decode_data (model : RationalCostModel) (W : ℕ) (f : Farey.Fraction) : (decode model W f).1=f.value := rfl

theorem decode_work (model : RationalCostModel) (W B : ℕ) (f : Farey.Fraction) (hn : f.num≤B) (hd : f.den≤B) :
    (decode model W f).2≤6*model.rat (1+2*binaryWordWidth B)+32*W := by
  let Q := model.rat (1+2*binaryWordWidth B)
  have hNatN := model.monotone ((Nat.add_le_add_left (binaryWordWidth_mono hn) 1).trans
    (show 1+binaryWordWidth B≤1+2*binaryWordWidth B by omega))
  have hNatD := model.monotone ((Nat.add_le_add_left (binaryWordWidth_mono hd) 1).trans
    (show 1+binaryWordWidth B≤1+2*binaryWordWidth B by omega))
  have hN : RationalHeight (f.num:ℚ) (binaryWordWidth B) := by
    simpa only [Int.cast_natCast] using GeneralPaperBasisStageSize.int_height (f.num:ℤ) B (by simpa only [Int.natAbs_natCast] using hn)
  have hD : RationalHeight (f.den:ℚ) (binaryWordWidth B) := by
    simpa only [Int.cast_natCast] using GeneralPaperBasisStageSize.int_height (f.den:ℤ) B (by simpa only [Int.natAbs_natCast] using hd)
  have hV : RationalHeight ((f.num:ℚ)/(f.den:ℚ)) (binaryWordWidth B) := by
    simpa only [Int.cast_natCast] using RationalHeight.fraction (f.num:ℤ) f.den (binaryWordWidth B) f.den_pos
      (by simpa only [Int.natAbs_natCast] using hn.trans_lt (lt_pow_binaryWordWidth B)) (hd.trans_lt (lt_pow_binaryWordWidth B))
  have hRatN := model.monotone (rationalWordWidth_of_height hN)
  have hRatD := model.monotone (rationalWordWidth_of_height hD)
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    (f.num:ℚ) (f.den:ℚ) (1+2*binaryWordWidth B) (rationalWordWidth_of_height hN)
    (rationalWordWidth_of_height hD) (rationalWordWidth_of_height hV)
  change _≤6*Q+32*W
  dsimp only [decode]
  omega

def run {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (x : Input m k Qv b) :
    Option (Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)×ℕ :=
  let rho := decode model W x.classified.choice.proxy
  let rich := GeneralPaperCachedSharedPreparation.fromCache model.rat W k x.alphabet x.grid weights 1 rho.1
  let poor := GeneralPaperCachedSharedPreparation.fromCache model.rat W k x.alphabet x.grid weights rho.1 1
  let hRich := GeneralPaperCachedSharedPreparation.data model.rat W k Qv x.alphabet x.grid x.grid_data weights 1 rho.1
  let hPoor := GeneralPaperCachedSharedPreparation.data model.rat W k Qv x.alphabet x.grid x.grid_data weights rho.1 1
  let hRT : rich.1.trajectory.rows=x.grid.source.controls.trajectory.rows := by rw [hRich,rows_data x];rfl
  let hPT : poor.1.trajectory.rows=x.grid.source.controls.trajectory.rows := by rw [hPoor,rows_data x];rfl
  let hT : 0<x.grid.source.controls.trajectory.rows := by rw [rows_data x];exact GeneralPaperTrajectoryParameters.rows_positive x.alphabet.lambda k
  let hK : 0<x.control.proxy.K := by rw [canonical_labels x];exact GeneralPaperScoreScaleParameters.labels_positive m k
  let hDiv : x.control.proxy.K∣x.grid.source.controls.trajectory.rows := by
    rw [canonical_labels x,canonical_rows x]
    exact GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k
  let hQ : 0<x.control.proxy.Qg := by rw [x.control_data];exact grid_positive m k
  let compiled := GeneralPaperPreparedBitCompilerPair.run model W k Qv hQv weights hp hw x.control hQ x.alphabet
    x.grid.source (source_data x) x.classified rho.1 rich.1 poor.1 hRich hPoor hRT hPT hT hK hDiv
  (compiled.1.map (GeneralPaperColumnPairReindex.run (canonical_rows x) (canonical_labels x)),
    rho.2+rich.2+poor.2+compiled.2+128*W)

theorem data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (x : Input m k Qv b) :
    (run model W k Qv hQv weights hp hw b x).1=(GeneralPaperCachedSourcePair.run model k Qv hQv weights hp hw b x).1 := by
  obtain ⟨control,a,grid,classified,hControl,hA,hGrid,hClass⟩ := x
  subst control;subst a;subst grid;subst classified
  let g := GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv
  let rho := (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
  let rich := (GeneralPaperCachedSharedPreparation.fromCache model.rat W k (alphabet m k) g weights 1 rho).1
  let poor := (GeneralPaperCachedSharedPreparation.fromCache model.rat W k (alphabet m k) g weights rho 1).1
  have hr : rich=prepare (alphabet m k) k Qv weights 1 rho :=
    GeneralPaperCachedSharedPreparation.data model.rat W k Qv (alphabet m k) g rfl weights 1 rho
  have hp' : poor=prepare (alphabet m k) k Qv weights rho 1 :=
    GeneralPaperCachedSharedPreparation.data model.rat W k Qv (alphabet m k) g rfl weights rho 1
  have hRT : rich.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hr];rfl
  have hPT : poor.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hp'];rfl
  have hPair := GeneralPaperPreparedBitCompilerPair.data model W k Qv hm hQv weights hp hw b hb g.source rfl rich poor hr hp' hRT hPT
  have hR := GeneralPaperCachedSharedPreparation.same_data model.rat W k Qv (alphabet m k) g rfl weights 1 rho
  have hP := GeneralPaperCachedSharedPreparation.same_data model.rat W k Qv (alphabet m k) g rfl weights rho 1
  dsimp only [rich,poor] at hPair
  dsimp only [run,GeneralPaperCachedSourcePair.run]
  simp only [decode_data]
  erw [GeneralPaperColumnPairReindex.map_reflexive,GeneralPaperColumnPairReindex.map_reflexive]
  refine hPair.trans ?_
  congr 1

end Blotto.GeneralPaperCachedBitSourcePair
