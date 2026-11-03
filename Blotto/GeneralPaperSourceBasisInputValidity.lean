import Blotto.GeneralPaperBasisControllerWork

/-! The selected geometric source, original-grid decode and classifier's
auxiliary numerator supply the actual shared controller's feasible start.
No feasible-grid or positive-auxiliary oracle is supplied by the caller.
-/
namespace Blotto.GeneralPaperSourceBasisInputValidity
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls
open GeneralPaperBasisGridInputs GeneralPaperBasisCoordinates
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem actual_start {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S)
      prep.threshold ((inputs.betaN:ℝ)/(inputs.controls.N:ℝ))
      (fun a => (inputs.initialGrid.read (index a):ℝ)/(inputs.controls.N:ℝ)) := by
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let c := controls m k b reciprocal
  let initial := GeneralPaperSourceBasis.initialCoordinates k Qv hQv weights hp hs b reciprocal
  have hSource := GeneralPaperSourceInitializer.sound k Qv hm hQv weights hp hs b hb reciprocal
  have hn : 0<c.N := (positive m k hm b hb reciprocal).1
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hpF : 0<f.num := hf.1
  have hqF : 0<f.den := hpF.trans hf.2.1
  have hGrid (a : Variable m (prepare m k).K) : OnRationalLattice c.N (initial a) := hSource.2.2 a.1 _
  have hBudget : (auxiliaryNumerator m (prepare m k).H f.num f.den reciprocal:ℝ)/(c.N:ℝ)=(c.auxiliary:ℝ) := by
    have hh := congrArg (fun r : ℚ => (r:ℝ)) (auxiliary_decode m (prepare m k).H f.num f.den reciprocal hm (H_positive m k) hpF hqF)
    simpa only [c,f,controls,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh
  have hPoint (a : Variable m (prepare m k).K) : ((grid c.N initial).read (index a):ℝ)/(c.N:ℝ)=(initial a:ℝ) := by
    have hh := congrArg (fun r : ℚ => (r:ℝ)) (grid_decode c.N hn initial hGrid a)
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh
  change GeneralPaperAffineConstraintRows.Feasible _ _ _
    ((auxiliaryNumerator m (prepare m k).H f.num f.den reciprocal:ℝ)/(c.N:ℝ))
    (fun a => ((grid c.N initial).read (index a):ℝ)/(c.N:ℝ))
  rw [hBudget]
  simp only [hPoint]
  change GeneralPaperAffineConstraintRows.Feasible _ _ _ (c.auxiliary:ℝ)
    (GeneralPaperTransferPolytopePoint.coordinates (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal))
  exact hSource.2.1

end Blotto.GeneralPaperSourceBasisInputValidity
