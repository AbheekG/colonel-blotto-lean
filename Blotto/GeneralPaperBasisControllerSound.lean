import Blotto.GeneralPaperBasisController

/-! Every executed stage succeeds and preserves original-row provenance,
nonsingular cache and feasibility, including all zero-length extensions.
The final result is a full original defining basis at a feasible point.
-/
namespace Blotto.GeneralPaperBasisControllerSound
open RationalOrderCell GeneralPaperStrictScore GeneralPaperBasisStoredProducts GeneralPaperBasisState
open GeneralPaperBasisInvariant GeneralPaperBasisController GeneralPaperBasisCoordinates
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem stages_valid {T m K : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1)))
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => (initialGrid.read (index a):ℝ)/(N:ℝ))) (j : ℕ) (hj : j≤m*(K-1)) :
    ∃ state,stages dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid j hj=some state ∧
      Invariant dict v S h N betaN initialGrid hj state := by
  induction j with
  | zero => exact ⟨initial _,rfl,initial_valid dict v S h N betaN initialGrid hStart⟩
  | succ j ih =>
    obtain ⟨state,hRun,inv⟩ := ih (Nat.le_trans (Nat.le_succ j) hj)
    obtain ⟨newState,hStep,hInv⟩ := GeneralPaperBasisStepSound.step_valid scoreDepth dict v hK S h N hN hCap betaN
      initialGrid state (Nat.lt_of_succ_le hj) inv
    refine ⟨newState,?_,hInv⟩
    simp only [stages,hRun,Option.bind_some,hStep]

theorem run_valid {T m K : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1)))
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => (initialGrid.read (index a):ℝ)/(N:ℝ))) :
    ∃ state,run scoreDepth dict v S h N betaN initialGrid=some state ∧
      Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state := by
  exact stages_valid scoreDepth dict v hK S h N hN hCap betaN initialGrid hStart _ (Nat.le_refl _)

end Blotto.GeneralPaperBasisControllerSound
