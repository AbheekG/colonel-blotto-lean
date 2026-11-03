import Blotto.GeneralPaperBasisEndpointSize

/-! The actual source-fed checked endpoint returns short entries on the
original N-free common denominator. All basis, endpoint feasibility and
ratio-size premises come from actual execution and classifier results.
-/
namespace Blotto.GeneralPaperSourceEndpointSize
open GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

def Contract {m : ℕ} (k : ℕ) (gamma : ℚ)
    (point : GeneralPaperBasisRationalSolve.RatVector (m*((prepare m k).K-1))) (D : ℕ) : Prop :=
  0<D ∧ D≤(prepare m k).H ∧ ∀ a : RationalOrderCell.Variable m (prepare m k).K,
    OnRationalLattice (gamma.den*D) (reader point a) ∧
      RationalHeight (reader point a) (binaryWordWidth (prepare m k).qbar+binaryWordWidth (prepare m k).H)

theorem rich {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    ∃ point D,GeneralPaperCheckedSourceEndpoint.run k Qv hQv weights hp hs b false=some point ∧
      Contract k (GeneralPaperProxyClassifier.classify m k b).choice.endpoint point D := by
  rw [GeneralPaperCheckedSourceEndpoint.rich_eq k Qv hm hQv weights hp hs b hb hModify]
  obtain ⟨state,hRun,inv⟩ := GeneralPaperSourceBasis.run_valid k Qv hm hQv weights hp hs b hb false
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b false
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let gamma := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  have hCont := GeneralPaperBasisEndpointContinuation.rich k hm prep.dictionary v (prepare m k).S prep.threshold _
    (positive m k hm b hb false).1 _ _ state inv b hb hModify
    (GeneralPaperBasisContinuationControls.auxiliary_value m k hm b hb false)
  have hEnd := GeneralPaperSourceBasisEndpoint.evaluated_feasible prep.dictionary v (prepare m k).S prep.threshold
    state inv.nonzero gamma hCont
  have hModified : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by simp [hModify]
  have hGamma := GeneralPaperEndpointRatioSize.denominator m k b hModified
  refine ⟨(GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1,state.determinant.natAbs,
    ?_,Int.natAbs_pos.mpr inv.nonzero,GeneralPaperBasisEndpointSize.determinant_H k hm prep.dictionary v _ _ _ _ _ state inv,?_⟩
  · simp only [GeneralPaperSourceBasisEndpoint.run,Bool.false_eq_true,false_and,ite_false,hRun,Option.map_some,gamma]
  · intro a
    exact ⟨GeneralPaperBasisAffineEvaluate.rational_lattice (GeneralPaperBasisAffineData.prepare state) inv.nonzero gamma
        (GeneralPaperBasisCoordinates.index a),
      GeneralPaperBasisEndpointSize.entry_height k hm prep.dictionary v _ _ _ _ _ state inv gamma hGamma hEnd a⟩

theorem poor {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hEndpoint : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) :
    ∃ point D,GeneralPaperCheckedSourceEndpoint.run k Qv hQv weights hp hs b true=some point ∧
      Contract k (1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) point D := by
  rw [GeneralPaperCheckedSourceEndpoint.poor_eq k Qv hm hQv weights hp hs b hb hModify hEndpoint]
  obtain ⟨state,hRun,inv⟩ := GeneralPaperSourceBasis.run_valid k Qv hm hQv weights hp hs b hb true
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let gamma : ℚ := 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  have hCont := GeneralPaperBasisEndpointContinuation.poor k hm prep.dictionary v (prepare m k).S prep.threshold _
    (positive m k hm b hb true).1 _ _ state inv b hb hModify hEndpoint
    (GeneralPaperBasisContinuationControls.auxiliary_value m k hm b hb true)
  have hRat : GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S)
      prep.threshold (gamma:ℝ) (fun a => GeneralPaperBasisAffineSystem.value (GeneralPaperBasisAffineData.prepare state) (gamma:ℝ)
        (GeneralPaperBasisCoordinates.index a)) := by
    simpa only [gamma,Rat.cast_div,Rat.cast_one] using hCont
  have hEnd := GeneralPaperSourceBasisEndpoint.evaluated_feasible prep.dictionary v (prepare m k).S prep.threshold
    state inv.nonzero gamma hRat
  have hModified : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by simp [hModify]
  have hGamma := GeneralPaperEndpointRatioSize.threshold_denominator m k b hb hModified true
  refine ⟨(GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1,state.determinant.natAbs,
    ?_,Int.natAbs_pos.mpr inv.nonzero,GeneralPaperBasisEndpointSize.determinant_H k hm prep.dictionary v _ _ _ _ _ state inv,?_⟩
  · have he : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint≠0 := by exact_mod_cast hEndpoint.ne'
    simp only [GeneralPaperSourceBasisEndpoint.run,he,and_false,ite_false,ite_true,hRun,Option.map_some,gamma]
  · intro a
    exact ⟨GeneralPaperBasisAffineEvaluate.rational_lattice (GeneralPaperBasisAffineData.prepare state) inv.nonzero gamma
        (GeneralPaperBasisCoordinates.index a),
      GeneralPaperBasisEndpointSize.entry_height k hm prep.dictionary v _ _ _ _ _ state inv gamma hGamma hEnd a⟩

theorem poor_numerator_denominator {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hEndpoint : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) :
    ∃ point D,GeneralPaperCheckedSourceEndpoint.run k Qv hQv weights hp hs b true=some point ∧
      Contract k (1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) point D ∧
      ∀ a : RationalOrderCell.Variable m (prepare m k).K,
        OnRationalLattice ((GeneralPaperProxyClassifier.classify m k b).choice.endpoint.num.natAbs*D) (reader point a) := by
  obtain ⟨point,D,hr,hc⟩ := poor k Qv hm hQv weights hp hs b hb hModify hEndpoint
  have he : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint≠0 := by exact_mod_cast hEndpoint.ne'
  refine ⟨point,D,hr,hc,?_⟩
  intro a
  have hd : (1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℚ).den=
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint.num.natAbs := by
    simp only [one_div,Rat.den_inv_of_ne_zero he]
  rw [←hd]
  exact (hc.2.2 a).1

end Blotto.GeneralPaperSourceEndpointSize
