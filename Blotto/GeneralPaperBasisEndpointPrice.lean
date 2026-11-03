import Blotto.GeneralPaperEndpointBits

/-! Every valid original-basis stage supplies the rational lattice,
magnitude, feasible-start and unit-velocity premises of the complete ray
price. This prices the ray phase on already computed point/direction data;
their preparation, matrix construction and basis update are separate phases.
Global integer/index/reference word capacities remain explicit in bits.
-/
namespace Blotto.GeneralPaperBasisEndpointPrice
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisOriginalDirection GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4096

theorem arithmetic {T m j : ℕ} (k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state) :
    (GeneralPaperEndpointWork.run dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h
      ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)).2≤
      GeneralPaperEndpointPriceControl.profile T m (prepare m k).K S 1 1 := by
  have hx := GeneralPaperRayAnchorBound.point k dict v S h N hN betaN initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hb := GeneralPaperRayAnchorBound.budget N hN state.determinant.natAbs betaN
  obtain ⟨a,_⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hK : 2≤(prepare m k).K := by have hh := a.2.isLt; omega
  exact GeneralPaperEndpointWork.work (N*state.determinant.natAbs) state.determinant.natAbs
    1 (j*(prepare m k).H*(m+1)+1) betaN.natAbs hm hK
    (Nat.mul_pos hN (Int.natAbs_pos.mpr inv.nonzero)) (Int.natAbs_pos.mpr inv.nonzero) _ _ S h _ _ _ hx hw hb

theorem bits {T m j : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (hK : 0<(prepare m k).K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*((prepare m k).K-1))) (state : State j (m*((prepare m k).K-1)))
    (hj : j<m*((prepare m k).K-1)) (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (hW : 1≤W) (hWordK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth (S+4)≤W) :
    (GeneralPaperEndpointBits.run model W dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h
      ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)).2≤
      GeneralPaperEndpointPriceControl.profile T m (prepare m k).K S W
        (model.rat (6*GeneralPaperRayUniformSize.width (N*state.determinant.natAbs) state.determinant.natAbs
          m 1 (j*(prepare m k).H*(m+1)+1) betaN.natAbs+9)) := by
  have hx := GeneralPaperRayAnchorBound.point k dict v S h N hN betaN initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hb := GeneralPaperRayAnchorBound.budget N hN state.determinant.natAbs betaN
  obtain ⟨a,ha⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hStart : GeneralPaperAffineConstraintRows.Feasible dict.label
      (GeneralPaperRayQueryWork.scores (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1) h
      (((betaN:ℚ)/(N:ℚ):ℚ):ℝ)
      (fun b => (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point b:ℝ)) := by
    rw [GeneralPaperRayInitialQuery.actual_scores scoreDepth dict v S hK hCap]
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  exact GeneralPaperEndpointBits.work model W (N*state.determinant.natAbs) state.determinant.natAbs
    1 (j*(prepare m k).H*(m+1)+1) betaN.natAbs
    (Nat.mul_pos hN (Int.natAbs_pos.mpr inv.nonzero)) (Int.natAbs_pos.mpr inv.nonzero) (Nat.dvd_mul_left _ _)
    _ _ S h _ _ _ hx hw hb hStart a ha hW hWordK hM hIndex hBatch hFinalIndex

end Blotto.GeneralPaperBasisEndpointPrice
