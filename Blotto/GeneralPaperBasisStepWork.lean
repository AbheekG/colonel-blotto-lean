import Blotto.GeneralPaperBasisAdvanceWork

/-! Actual fresh point/direction preparation, complete ray execution and
conditional original-row cache extension, with every unit-arithmetic phase
and branch charged. No source, endpoint or callback-cost oracle is supplied.
-/
namespace Blotto.GeneralPaperBasisStepWork
open RationalOrderCell GeneralPaperBasisState GeneralPaperBasisStoredProducts GeneralPaperBasisInvariant
open GeneralPaperBasisOriginalDirection GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4096

def run {T m K j : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (state : State j (m*(K-1))) (hj : j<m*(K-1)) :
    Option (State (j+1) (m*(K-1))) × ℕ :=
  let point := GeneralPaperBasisPreparationWork.point N betaN state.determinant state.adjugate state.rows initialGrid
  let velocity := GeneralPaperBasisPreparationWork.direction state.determinant state.adjugate state.rows (next hj)
  let ray := GeneralPaperEndpointWork.run labels matrix S h ((betaN:ℚ)/(N:ℚ)) (reader point.point) (reader velocity.velocity)
  match ray.1 with
  | none => (none,point.work+velocity.work+ray.2+24)
  | some answer =>
    let updated := GeneralPaperBasisAdvanceWork.run labels state hj answer
    (some updated.1,point.work+velocity.work+ray.2+updated.2+32)

theorem data {T m K j : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (state : State j (m*(K-1))) (hj : j<m*(K-1)) :
    (run labels matrix S h N betaN initialGrid state hj).1=step labels matrix S h N betaN initialGrid state hj := by
  unfold run step
  simp only [GeneralPaperBasisPreparationWork.point_data,GeneralPaperBasisPreparationWork.direction_data,GeneralPaperEndpointWork.data]
  cases GeneralPaperRayEndpoint.prepared labels matrix S h ((betaN:ℚ)/(N:ℚ))
    (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
    (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)
  · rfl
  · simp only [GeneralPaperBasisAdvanceWork.data,Option.map_some]

def profile (T m K S : ℕ) : ℕ :=
  2048*(m*(K-1)+1)*(2*(m*(K-1))+2)+GeneralPaperBasisAdvanceWork.profile (m*(K-1)) (m*(K-1)) m+
    GeneralPaperEndpointPriceControl.profile T m K S 1 1+32

theorem work {T m j : ℕ} (k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state) :
    (run dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid state hj).2≤
      profile T m (prepare m k).K S := by
  let point := GeneralPaperBasisPreparationWork.point N betaN state.determinant state.adjugate state.rows initialGrid
  let velocity := GeneralPaperBasisPreparationWork.direction state.determinant state.adjugate state.rows (next hj)
  let ray := GeneralPaperEndpointWork.run dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h
    ((betaN:ℚ)/(N:ℚ)) (reader point.point) (reader velocity.velocity)
  have hPoint := GeneralPaperBasisPreparationWork.point_work N betaN state.determinant state.adjugate state.rows initialGrid
  have hVelocity := GeneralPaperBasisPreparationWork.direction_work state.determinant state.adjugate state.rows (next hj)
  have hRay : ray.2≤GeneralPaperEndpointPriceControl.profile T m (prepare m k).K S 1 1 := by
    dsimp only [ray]
    rw [GeneralPaperBasisPreparationWork.point_data,GeneralPaperBasisPreparationWork.direction_data]
    exact GeneralPaperBasisEndpointPrice.arithmetic k hm scoreDepth dict v S h N hN betaN initialGrid state hj inv
  have hPreparation : point.work+velocity.work≤2048*(m*((prepare m k).K-1)+1)*(2*(m*((prepare m k).K-1))+2) := by
    have hh := Nat.mul_le_mul (by omega : j+1≤m*((prepare m k).K-1)+1)
      (by omega : j+m*((prepare m k).K-1)+2≤2*(m*((prepare m k).K-1))+2)
    have hp := Nat.mul_le_mul_left 2048 hh
    nlinarith only [hPoint,hVelocity,hp]
  change ray.2≤_ at hRay
  rw [run]
  cases hr : ray.1 with
  | none =>
    change point.work+velocity.work+ray.2+24≤profile T m (prepare m k).K S
    unfold profile
    omega
  | some answer =>
    have hAdvance := (GeneralPaperBasisAdvanceWork.work hm dict.label state hj answer).trans
      (GeneralPaperBasisAdvanceWork.profile_mono j (m*((prepare m k).K-1)) m (Nat.le_of_lt hj))
    change point.work+velocity.work+ray.2+(GeneralPaperBasisAdvanceWork.run dict.label state hj answer).2+32≤profile T m (prepare m k).K S
    unfold profile
    omega

end Blotto.GeneralPaperBasisStepWork
