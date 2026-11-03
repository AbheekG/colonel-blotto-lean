import Blotto.GeneralPaperRayOperandWidthEnvelope

/-! The ACTUAL prepared source and shared matrix supply all premises of
the native ray parameter-height theorem and its paper logarithmic envelope.
No grid, affine, endpoint or ratio-size certificate is supplied by a caller.
The invariant is the established native controller stage invariant.
-/
namespace Blotto.GeneralPaperSourceRayOperandSize
open GeneralPaperProxyParameters GeneralPaperBasisStoredProducts GeneralPaperBasisInvariant GeneralPaperBasisState
open GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem stage {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      ∃ answer,GeneralPaperRayEndpoint.prepared prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))
        (reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point)
        (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)=some answer ∧
        RationalHeight answer.time
          (78+binaryWordWidth inputs.controls.N+14*((prepare m k).d+2)*binaryWordWidth (m+3)+
            12*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+(prepare m k).S+
              (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+2)) ∧
        GeneralPaperBasisAdvanceSize.Contract k prep.dictionary.label state hj answer := by
  dsimp only
  intro j hj state inv
  have hn := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨answer,hr,hSize,hUpdate⟩ := GeneralPaperRayEndpointSize.stage_return k hm (GeneralPaperScoreScaleParameters.prepare m k).depth
    _ _ (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S _ _ hn
    (GeneralPaperScoreScaleParameters.score_cap m k) _ _ state hj inv
  have hDet := (GeneralPaperBasisCacheSize.cache_H k hm _ _ _ _ _ _ _ (Nat.le_of_lt hj) state inv).1
  have hBeta := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hEnvelope := GeneralPaperRayOperandWidthEnvelope.paper_envelope m k j
    (GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N state.determinant.natAbs _
    (prepare m k).S (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows hj.le hDet hBeta
  refine ⟨answer,?_,hSize.mono hEnvelope,hUpdate⟩
  rw [GeneralPaperSharedBasisInputs.matrix_eq]
  exact hr

end Blotto.GeneralPaperSourceRayOperandSize
