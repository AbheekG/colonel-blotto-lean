import Blotto.GeneralPaperBasisStepBits

/-! Complete bit-priced d-stage controller on one prepared score matrix.
Every reached concrete stage price follows from native invariants. Initial,
zero-stage, failure and return data are unchanged. Matrix/source/grid
preparation and full global word/space joins remain separate phases.
-/
namespace Blotto.GeneralPaperBasisControllerBits
open RationalOrderCell GeneralPaperBasisState GeneralPaperBasisStoredProducts GeneralPaperBasisInvariant
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def stages {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) : (j : ℕ) → j≤m*(K-1) → Option (State j (m*(K-1))) × ℕ
  | 0,_ =>
    let empty := GeneralPaperBasisArrayPrice.initialRun (fun w => w) W (m*(K-1))
    (some empty.1,empty.2+8*W)
  | j+1,hj =>
    let earlier := stages model W labels matrix S h N betaN initialGrid j (Nat.le_trans (Nat.le_succ j) hj)
    match earlier.1 with
    | none => (none,earlier.2+8*W)
    | some state =>
      let updated := GeneralPaperBasisStepBits.run model W labels matrix S h N betaN initialGrid state (Nat.lt_of_succ_le hj)
      (updated.1,earlier.2+updated.2+24*W)

theorem stages_data {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (j : ℕ) (hj : j≤m*(K-1)) :
    (stages model W labels matrix S h N betaN initialGrid j hj).1=GeneralPaperBasisController.stages labels matrix S h N betaN initialGrid j hj := by
  induction j with
  | zero => simp only [stages,GeneralPaperBasisArrayPrice.initial_data,GeneralPaperBasisController.stages]
  | succ j ih =>
    rw [stages,GeneralPaperBasisController.stages]
    simp only [ih]
    cases GeneralPaperBasisController.stages labels matrix S h N betaN initialGrid j (Nat.le_trans (Nat.le_succ j) hj)
    · rfl
    · simp only [GeneralPaperBasisStepBits.data,Option.bind_some]

theorem stages_work {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hBeta : betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k) (hGrid : ∀ i,(initialGrid.read i).natAbs≤N)
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => (initialGrid.read (GeneralPaperBasisCoordinates.index a):ℝ)/(N:ℝ)))
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth (S+4)≤W) (j : ℕ) (hj : j≤m*((prepare m k).K-1)) :
    (stages model W dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid j hj).2≤
      72*W+j*(GeneralPaperBasisStepBits.profile T m (prepare m k).K S W (model.rat (GeneralPaperBasisBitEnvelope.width m k N S T))+24*W) := by
  induction j with
  | zero =>
    have hh := GeneralPaperBasisAppendBits.initial_work W (m*((prepare m k).K-1)) hW
    change (GeneralPaperBasisArrayPrice.initialRun (fun w => w) W (m*((prepare m k).K-1))).2+8*W≤_
    omega
  | succ j ih =>
    have hp := ih (Nat.le_trans (Nat.le_succ j) hj)
    obtain ⟨state,hs,inv⟩ := GeneralPaperBasisControllerSound.stages_valid scoreDepth dict v
      (GeneralPaperScoreScaleParameters.labels_positive m k) S h N hN hCap betaN initialGrid hStart j (Nat.le_trans (Nat.le_succ j) hj)
    have he : (stages model W dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid
        j (Nat.le_trans (Nat.le_succ j) hj)).1=some state := by rw [stages_data]; exact hs
    have hStep := GeneralPaperBasisStepBits.work model W k hm scoreDepth dict v S h N hN hCap betaN initialGrid state
      (Nat.lt_of_succ_le hj) inv hBeta hGrid hW hDim hIndex hBatch hFinal
    rw [stages,he]
    dsimp only
    nlinarith only [hp,hStep]

def profile (T m K S W Q : ℕ) : ℕ := 72*W+(m*(K-1))*(GeneralPaperBasisStepBits.profile T m K S W Q+24*W)

theorem profile_bound (T m K S W Q : ℕ) : profile T m K S W Q≤262144*(m*(K-1)+3)^3*(W+Q)+
    (m*(K-1))*GeneralPaperEndpointPriceControl.profile T m K S W Q := by
  let d := m*(K-1)
  change 72*W+d*(131072*(d+1)^2*(W+Q)+GeneralPaperEndpointPriceControl.profile T m K S W Q+24*W)≤
    262144*(d+3)^3*(W+Q)+d*GeneralPaperEndpointPriceControl.profile T m K S W Q
  nlinarith only [Nat.zero_le (d^3*W),Nat.zero_le (d^2*W),Nat.zero_le (d*W),Nat.zero_le W,
    Nat.zero_le (d^3*Q),Nat.zero_le (d^2*Q),Nat.zero_le (d*Q),Nat.zero_le Q]

end Blotto.GeneralPaperBasisControllerBits
