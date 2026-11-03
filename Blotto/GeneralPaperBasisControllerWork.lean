import Blotto.GeneralPaperBasisStepWork
import Blotto.GeneralPaperScoreMatrixUnit

/-! The complete d-stage original-basis controller, with one initial empty
cache and one prepared score matrix. Every reached stage is charged once;
native invariant preservation discharges its concrete solve/ray/update price.
Zero stages and failed returns retain their exact native behavior.
-/
namespace Blotto.GeneralPaperBasisControllerWork
open RationalOrderCell GeneralPaperBasisState GeneralPaperBasisStoredProducts GeneralPaperBasisInvariant
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def stages {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) : (j : ℕ) → j≤m*(K-1) → Option (State j (m*(K-1))) × ℕ
  | 0,_ =>
    let empty := GeneralPaperBasisArrayPrice.initialRun (fun _ => 1) 1 (m*(K-1))
    (some empty.1,empty.2+8)
  | j+1,hj =>
    let earlier := stages labels matrix S h N betaN initialGrid j (Nat.le_trans (Nat.le_succ j) hj)
    match earlier.1 with
    | none => (none,earlier.2+8)
    | some state =>
      let updated := GeneralPaperBasisStepWork.run labels matrix S h N betaN initialGrid state (Nat.lt_of_succ_le hj)
      (updated.1,earlier.2+updated.2+24)

theorem stages_data {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (j : ℕ) (hj : j≤m*(K-1)) :
    (stages labels matrix S h N betaN initialGrid j hj).1=
      GeneralPaperBasisController.stages labels matrix S h N betaN initialGrid j hj := by
  induction j with
  | zero => simp only [stages,GeneralPaperBasisArrayPrice.initial_data,GeneralPaperBasisController.stages]
  | succ j ih =>
    rw [stages,GeneralPaperBasisController.stages]
    simp only [ih]
    cases GeneralPaperBasisController.stages labels matrix S h N betaN initialGrid j (Nat.le_trans (Nat.le_succ j) hj)
    · rfl
    · simp only [GeneralPaperBasisStepWork.data,Option.bind_some]

def run {T m K : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) :
    Option (State (m*(K-1)) (m*(K-1))) × ℕ :=
  let matrix := GeneralPaperScoreMatrixUnit.run scoreDepth dict v S
  let result := stages dict.label matrix.1 S h N betaN initialGrid (m*(K-1)) (Nat.le_refl _)
  (result.1,matrix.2+result.2+16)

theorem data {T m K : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) :
    (run scoreDepth dict v S h N betaN initialGrid).1=GeneralPaperBasisController.run scoreDepth dict v S h N betaN initialGrid := by
  simp only [run,GeneralPaperScoreMatrixUnit.data,stages_data,GeneralPaperBasisController.run]

theorem stages_work {T m : ℕ} (k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (hK : 0<(prepare m k).K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*((prepare m k).K-1)))
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => (initialGrid.read (GeneralPaperBasisCoordinates.index a):ℝ)/(N:ℝ))) (j : ℕ) (hj : j≤m*((prepare m k).K-1)) :
    (stages dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid j hj).2≤
      72+j*(GeneralPaperBasisStepWork.profile T m (prepare m k).K S+24) := by
  induction j with
  | zero =>
    have hh := GeneralPaperBasisArrayPrice.initial_work (m*((prepare m k).K-1))
    change (GeneralPaperBasisArrayPrice.initialRun (fun _ => 1) 1 (m*((prepare m k).K-1))).2+8≤_
    omega
  | succ j ih =>
    have hp := ih (Nat.le_trans (Nat.le_succ j) hj)
    obtain ⟨state,hs,inv⟩ := GeneralPaperBasisControllerSound.stages_valid scoreDepth dict v hK S h N hN hCap betaN initialGrid hStart
      j (Nat.le_trans (Nat.le_succ j) hj)
    have he : (stages dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid
        j (Nat.le_trans (Nat.le_succ j) hj)).1=some state := by rw [stages_data]; exact hs
    have hStep := GeneralPaperBasisStepWork.work k hm scoreDepth dict v S h N hN betaN initialGrid state (Nat.lt_of_succ_le hj) inv
    rw [stages,he]
    dsimp only
    nlinarith only [hp,hStep]

def profile (scoreDepth T m K S : ℕ) : ℕ :=
  256*(m+1)*(K+1)*(scoreDepth+1)+72+(m*(K-1))*(GeneralPaperBasisStepWork.profile T m K S+24)+16

theorem work {T m : ℕ} (k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (hK : 0<(prepare m k).K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*((prepare m k).K-1)))
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => (initialGrid.read (GeneralPaperBasisCoordinates.index a):ℝ)/(N:ℝ))) :
    (run scoreDepth dict v S h N betaN initialGrid).2≤profile scoreDepth T m (prepare m k).K S := by
  have hMatrix := GeneralPaperScoreMatrixUnit.work scoreDepth dict v S
  have hStages := stages_work k hm scoreDepth dict v hK S h N hN hCap betaN initialGrid hStart _ (Nat.le_refl _)
  change (GeneralPaperScoreMatrixUnit.run scoreDepth dict v S).2+_+16≤_
  rw [GeneralPaperScoreMatrixUnit.data]
  unfold profile
  omega

theorem profile_bound (scoreDepth T m K S : ℕ) (hK : 2≤K) :
    profile scoreDepth T m K S≤256*(m+1)*(K+1)*(scoreDepth+1)+8192*(m*(K-1)+3)^3+
      (m*(K-1))*GeneralPaperEndpointPriceControl.profile T m K S 1 1 := by
  let d := m*(K-1)
  have hm : m≤d := by dsimp only [d]; nlinarith only [show 1≤K-1 by omega]
  have hStage : 2048*(d+1)*(2*d+2)+GeneralPaperBasisAdvanceWork.profile d d m+56≤8192*(d+3)^2 := by
    unfold GeneralPaperBasisAdvanceWork.profile
    nlinarith only [hm]
  have hPay := Nat.mul_le_mul_left d hStage
  change 256*(m+1)*(K+1)*(scoreDepth+1)+72+d*(GeneralPaperBasisStepWork.profile T m K S+24)+16≤_
  unfold GeneralPaperBasisStepWork.profile
  change _≤256*(m+1)*(K+1)*(scoreDepth+1)+8192*(d+3)^3+d*GeneralPaperEndpointPriceControl.profile T m K S 1 1
  change _+72+d*(2048*(d+1)*(2*d+2)+GeneralPaperBasisAdvanceWork.profile d d m+
    GeneralPaperEndpointPriceControl.profile T m K S 1 1+32+24)+16≤_
  nlinarith only [hPay]

end Blotto.GeneralPaperBasisControllerWork
