import Blotto.GeneralPaperBasisCacheBits

/-! Every valid original-basis stage and its actual recovered ray blocker
supply all cache-update bit-price and exact-division premises. The native
cache operand envelope has the paper logarithmic dimension/H dependence.
This prices only the cache update on constructed row/column/prefix data.
-/
namespace Blotto.GeneralPaperBasisCacheStageBits
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisOriginalDirection GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem paper_width (m k j S T : ℕ) (hj : j≤m*((prepare m k).K-1)) :
    GeneralPaperBasisCacheBitFacts.width j (prepare m k).H (m+1)≤
      256+64*((prepare m k).d+2)*binaryWordWidth (m+3)+
        128*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+S+T+2) := by
  have hs := GeneralPaperBasisCacheBitFacts.width_bound j (prepare m k).H (m+1)
  simp only [Nat.add_assoc,Nat.reduceAdd] at hs
  have hH := GeneralPaperRayOperandWidthEnvelope.word_add (prepare m k).H 1
  have hOne : binaryWordWidth 1=1 := by decide
  have hHP := GeneralPaperProxyWidths.H_width m k
  have hj' : j≤(prepare m k).d := by rw [(GeneralPaperProxyParameters.data m k).2.2.1]; exact hj
  have hJ := binaryWordWidth_mono (show j+1≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  have hM := binaryWordWidth_mono (show m+2≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  nlinarith only [hs,hH,hOne,hHP,hJ,hM]

theorem from_ray {T m j : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K)
    (hContract : GeneralPaperRayEndpointSound.Contract (S:=S) dict v h ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity) answer)
    (hW : 1≤W) (hJ : binaryWordWidth (j+2)≤W) :
    let row := GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row dict.label answer.blocker)
    let u := (GeneralPaperBasisDirection.columnRun state.rows (next hj)).1
    let p := rowPrefix row (Nat.le_of_lt hj)
    (GeneralPaperBasisCacheBits.run model.rat W state.determinant state.adjugate u p (row.coefficients.read (next hj))).work≤
      4096*(j+2)^2*(W+model.rat (GeneralPaperBasisCacheBitFacts.width j (prepare m k).H (m+1))) := by
  have hc := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv
  have hb := GeneralPaperBasisAdvanceSize.from_ray k hm dict v S h N betaN initialGrid state hj inv answer hContract
  have hInv := GeneralPaperBasisStepSound.advance_valid dict v S h N hN betaN initialGrid state hj inv answer hContract
  dsimp only
  apply GeneralPaperBasisCacheBits.work model.rat model.monotone W (prepare m k).H (m+1) hW hJ
    state.determinant state.adjugate (GeneralPaperBasisFreshRHS.minor state.rows (Nat.le_of_lt hj)) _ _ _ inv.cache inv.nonzero
  · exact hInv.nonzero
  · exact hc.1
  · exact hc.2
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2.1

theorem actual_ray {T m j : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (hK : 0<(prepare m k).K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*((prepare m k).K-1))) (state : State j (m*((prepare m k).K-1)))
    (hj : j<m*((prepare m k).K-1)) (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (hW : 1≤W) (hJ : binaryWordWidth (j+2)≤W) :
    ∃ answer,GeneralPaperRayEndpoint.prepared dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h
      ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)=some answer ∧
      let row := GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row dict.label answer.blocker)
      let u := (GeneralPaperBasisDirection.columnRun state.rows (next hj)).1
      let p := rowPrefix row (Nat.le_of_lt hj)
      (GeneralPaperBasisCacheBits.run model.rat W state.determinant state.adjugate u p (row.coefficients.read (next hj))).work≤
        4096*(j+2)^2*(W+model.rat (256+64*((prepare m k).d+2)*binaryWordWidth (m+3)+
          128*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+S+T+2))) := by
  obtain ⟨a,ha⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h
      (((betaN:ℚ)/(N:ℚ):ℚ):ℝ)
      (fun b => (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point b:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  obtain ⟨answer,hr,hc⟩ := GeneralPaperRayEndpointSound.endpoint_sound scoreDepth dict v hK hCap h ((betaN:ℚ)/(N:ℚ)) _ _ hStart a ha
  refine ⟨answer,hr,?_⟩
  exact (from_ray model W k hm dict v S h N hN betaN initialGrid state hj inv answer hc hW hJ).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone (paper_width m k j S T (Nat.le_of_lt hj))) W))

end Blotto.GeneralPaperBasisCacheStageBits
