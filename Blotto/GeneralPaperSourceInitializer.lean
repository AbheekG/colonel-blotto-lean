import Blotto.GeneralPaperNativeRationalValues

/-! The actual own-tree geometric full source feeds the actual quantizer,
normalization, complete strict-score DP and native N-grid initializer.
Rational scores use exactly the source's own normalized integer weights.
No row-feasibility, high-tuple, gap or auxiliary-point oracle is supplied.
Original active-basis construction and endpoint continuation remain open.
-/
namespace Blotto.GeneralPaperSourceInitializer
open GeneralPaperInitializerPreparedPoint GeneralPaperInitializerSelectedControls GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def sourceRows {m : ℕ} (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℝ) (reciprocal : Bool) :
    FixedArrayTable (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (FixedArrayTable m ℚ) :=
  GeneralPaperCatalogueRationalTrajectory.rows (alphabet m k) k Qv (prepare m k).qbar weights
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)

theorem source_rows_feasible {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (i : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    Blotto.Feasible (ownBudget m k b reciprocal:ℝ) (fun j => (((sourceRows k Qv weights b reciprocal).read i).read j:ℝ)) := by
  let rho := (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
  have hCap := GeneralPaperProxyClassifier.proxy_reduced_denominator m k b
  have hDen : (ownBudget m k b reciprocal).den∣rho.den := by
    cases reciprocal <;> simp [ownBudget,rho]
  exact GeneralPaperCatalogueRationalTrajectory.every_row_feasible (alphabet m k) k Qv rho.den (prepare m k).qbar hm hQv weights hs
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) (own_positive m k b hb reciprocal).le
    (Rat.den_pos rho) hCap hDen i

noncomputable def prepared {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    GeneralPaperTransferPreparation.Prepared (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m
      (prepare m k).K (prepare m k).S :=
  GeneralPaperTransferPreparation.prepare (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (sourceRows k Qv weights b reciprocal) (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S

noncomputable def initial {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    GeneralPaperDictionary.Dictionary (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K :=
  let p := prepared k Qv hQv weights hp hs b reciprocal
  let c := controls m k b reciprocal
  GeneralPaperInitializerDictionary.build p.dictionary c.N c.depth

theorem sound {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let p := prepared k Qv hQv weights hp hs b reciprocal
    let c := controls m k b reciprocal
    let d := initial k Qv hQv weights hp hs b reciprocal
    GeneralPaperTransferPreparation.UnitDictionary d (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k) ∧
      GeneralPaperAffineConstraintRows.Feasible p.dictionary.label
        (GeneralPaperStrictScore.score (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S)
        p.threshold (c.auxiliary:ℝ) (GeneralPaperTransferPolytopePoint.coordinates d) ∧
      ∀ j l,OnRationalLattice c.N (d.anchor j l) :=
  GeneralPaperInitializerPreparedPoint.prepared k hm (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    b hb reciprocal (sourceRows k Qv weights b reciprocal) (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (prepare m k).S (source_rows_feasible k Qv hm hQv weights hs b hb reciprocal)

end Blotto.GeneralPaperSourceInitializer
