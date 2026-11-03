import Blotto.GeneralPaperSegmentCompilerStorage

/-! One phase-indexed envelope for all executed segment-compiler cursors and
returns. Earlier array owners and their price records stay live during later
phases; one shared environment is counted by the active phase. The calling
factory still owns environment construction, fixed code and outer controls. -/
namespace Blotto.GeneralPaperSegmentCompilerLifetime
open GeneralPaperEncodedBasisStorage (arrayFootprint)
open GeneralPaperSegmentExpressionCompiler (Programs row)
open GeneralPaperExpressionMatrixLifetime (matrix)
open GeneralPaperSegmentCompilerStorage (Bounds owner rowOwnerProfile matrixOwnerProfile)
set_option autoImplicit false
set_option maxHeartbeats 1600000

inductive Phase (n r : ℕ) where
  | weightActive (i : Fin r)
  | weightReturn
  | leftActive (i : Fin r) (j : Fin n)
  | leftRow (i : Fin r)
  | leftReturn
  | rightActive (i : Fin r) (j : Fin n)
  | rightRow (i : Fin r)
  | rightReturn
  | assembly

def window {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (p : Programs l env) (borrowed : ℕ) : Phase n r → ℕ :=
  let w := owner A (arrayFootprint A rationalWordWidth) (row model A env p.weight)
  let left := owner A (arrayFootprint A (arrayFootprint A rationalWordWidth)) (matrix model A env p.left)
  fun phase => match phase with
  | .weightActive i => GeneralPaperExpressionRowLifetime.sourceWindow model A env p.weight i.val i.isLt borrowed
  | .weightReturn => GeneralPaperExpressionArrayReturns.rowWindow model A env p.weight borrowed
  | .leftActive i j => GeneralPaperExpressionMatrixLifetime.activeWindow model A env p.left i.val i.isLt j.val j.isLt (borrowed + w)
  | .leftRow i => GeneralPaperExpressionArrayReturns.outerRowWindow model A env p.left i (borrowed + w)
  | .leftReturn => GeneralPaperExpressionArrayReturns.matrixWindow model A env p.left (borrowed + w)
  | .rightActive i j => GeneralPaperExpressionMatrixLifetime.activeWindow model A env p.right i.val i.isLt j.val j.isLt (borrowed + w + left)
  | .rightRow i => GeneralPaperExpressionArrayReturns.outerRowWindow model A env p.right i (borrowed + w + left)
  | .rightReturn => GeneralPaperExpressionArrayReturns.matrixWindow model A env p.right (borrowed + w + left)
  | .assembly => GeneralPaperSegmentCompilerStorage.assemblyWindow model A env p borrowed

def phaseProfile (model : RationalCostModel) (A n r k s d M borrowed : ℕ) : Phase n r → ℕ :=
  let W := rowOwnerProfile model A r k s d M
  let L := matrixOwnerProfile model A n r k s d M
  fun phase => match phase with
  | .weightActive _ => GeneralPaperExpressionRowLifetime.profile model A r k s d M borrowed
  | .weightReturn => GeneralPaperExpressionArrayReturns.rowProfile model A r k s d M borrowed
  | .leftActive _ _ => GeneralPaperExpressionMatrixLifetime.activeProfile model A n r k s d M (borrowed + W)
  | .leftRow _ => GeneralPaperExpressionArrayReturns.rowProfile model A n k s d M
      (borrowed + W + GeneralPaperExpressionMatrixLifetime.outerProfile model A n r k s d M)
  | .leftReturn => GeneralPaperExpressionArrayReturns.matrixProfile model A n r k s d M (borrowed + W)
  | .rightActive _ _ => GeneralPaperExpressionMatrixLifetime.activeProfile model A n r k s d M (borrowed + W + L)
  | .rightRow _ => GeneralPaperExpressionArrayReturns.rowProfile model A n k s d M
      (borrowed + W + L + GeneralPaperExpressionMatrixLifetime.outerProfile model A n r k s d M)
  | .rightReturn => GeneralPaperExpressionArrayReturns.matrixProfile model A n r k s d M (borrowed + W + L)
  | .assembly => GeneralPaperSegmentCompilerStorage.assemblyProfile model A n r k s d M borrowed

theorem phase_bound {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (p : Programs l env) (s d M : ℕ) (h : Bounds p s d M)
    (borrowed : ℕ) (phase : Phase n r) :
    window model A env p borrowed phase ≤ phaseProfile model A n r k s d M borrowed phase := by
  have hW := GeneralPaperSegmentCompilerStorage.row_owner model A env p.weight s d M
    h.environment h.weight_literals h.weight_depth h.weight_operations
  have hL := GeneralPaperSegmentCompilerStorage.matrix_owner model A env p.left s d M
    h.environment h.left_literals h.left_depth h.left_operations
  cases phase with
  | weightActive i =>
    exact GeneralPaperExpressionRowLifetime.actual model A env p.weight s d M
      h.environment h.weight_literals h.weight_depth h.weight_operations i.val i.isLt borrowed
  | weightReturn =>
    exact GeneralPaperExpressionArrayReturns.row_return model A env p.weight s d M
      h.environment h.weight_literals h.weight_depth h.weight_operations borrowed
  | leftActive i j =>
    have hPhase := GeneralPaperExpressionMatrixLifetime.active model A env p.left s d M
      h.environment h.left_literals h.left_depth h.left_operations i.val i.isLt j.val j.isLt (borrowed + owner A (arrayFootprint A rationalWordWidth) (row model A env p.weight))
    unfold window phaseProfile
    dsimp only
    apply hPhase.trans
    unfold GeneralPaperExpressionMatrixLifetime.activeProfile GeneralPaperExpressionRowLifetime.profile
    omega
  | leftRow i =>
    have hPhase := GeneralPaperExpressionArrayReturns.outer_row_return model A env p.left s d M
      h.environment h.left_literals h.left_depth h.left_operations i (borrowed + owner A (arrayFootprint A rationalWordWidth) (row model A env p.weight))
    unfold window phaseProfile
    dsimp only
    apply hPhase.trans
    unfold GeneralPaperExpressionArrayReturns.rowProfile
    omega
  | leftReturn =>
    have hPhase := GeneralPaperExpressionArrayReturns.matrix_return model A env p.left s d M
      h.environment h.left_literals h.left_depth h.left_operations  (borrowed + owner A (arrayFootprint A rationalWordWidth) (row model A env p.weight))
    unfold window phaseProfile
    dsimp only
    apply hPhase.trans
    unfold GeneralPaperExpressionArrayReturns.matrixProfile
    omega
  | rightActive i j =>
    have hPhase := GeneralPaperExpressionMatrixLifetime.active model A env p.right s d M
      h.environment h.right_literals h.right_depth h.right_operations i.val i.isLt j.val j.isLt (borrowed + owner A (arrayFootprint A rationalWordWidth) (row model A env p.weight) + owner A (arrayFootprint A (arrayFootprint A rationalWordWidth)) (matrix model A env p.left))
    unfold window phaseProfile
    dsimp only
    apply hPhase.trans
    unfold GeneralPaperExpressionMatrixLifetime.activeProfile GeneralPaperExpressionRowLifetime.profile
    omega
  | rightRow i =>
    have hPhase := GeneralPaperExpressionArrayReturns.outer_row_return model A env p.right s d M
      h.environment h.right_literals h.right_depth h.right_operations i (borrowed + owner A (arrayFootprint A rationalWordWidth) (row model A env p.weight) + owner A (arrayFootprint A (arrayFootprint A rationalWordWidth)) (matrix model A env p.left))
    unfold window phaseProfile
    dsimp only
    apply hPhase.trans
    unfold GeneralPaperExpressionArrayReturns.rowProfile
    omega
  | rightReturn =>
    have hPhase := GeneralPaperExpressionArrayReturns.matrix_return model A env p.right s d M
      h.environment h.right_literals h.right_depth h.right_operations  (borrowed + owner A (arrayFootprint A rationalWordWidth) (row model A env p.weight) + owner A (arrayFootprint A (arrayFootprint A rationalWordWidth)) (matrix model A env p.left))
    unfold window phaseProfile
    dsimp only
    apply hPhase.trans
    unfold GeneralPaperExpressionArrayReturns.matrixProfile
    omega
  | assembly => exact GeneralPaperSegmentCompilerStorage.assembly model A env p s d M h borrowed

def profile (model : RationalCostModel) (A n r k s d M borrowed : ℕ) : ℕ :=
  borrowed + rowOwnerProfile model A r k s d M + matrixOwnerProfile model A n r k s d M +
    GeneralPaperExpressionRowLifetime.profile model A r k s d M 0 +
    GeneralPaperExpressionArrayReturns.rowProfile model A r k s d M 0 +
    GeneralPaperExpressionMatrixLifetime.activeProfile model A n r k s d M 0 +
    GeneralPaperExpressionArrayReturns.rowProfile model A n k s d M
      (GeneralPaperExpressionMatrixLifetime.outerProfile model A n r k s d M) +
    GeneralPaperExpressionArrayReturns.matrixProfile model A n r k s d M 0 +
    GeneralPaperSegmentCompilerStorage.assemblyProfile model A n r k s d M 0

theorem all_phases {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (p : Programs l env) (s d M : ℕ) (h : Bounds p s d M)
    (borrowed : ℕ) (phase : Phase n r) :
    window model A env p borrowed phase ≤ profile model A n r k s d M borrowed := by
  apply (phase_bound model A env p s d M h borrowed phase).trans
  cases phase <;> simp only [phaseProfile, profile]
  all_goals
    unfold GeneralPaperExpressionMatrixLifetime.activeProfile GeneralPaperExpressionRowLifetime.profile
      GeneralPaperExpressionArrayReturns.rowProfile GeneralPaperExpressionArrayReturns.matrixProfile
      GeneralPaperSegmentCompilerStorage.assemblyProfile
  all_goals omega

end Blotto.GeneralPaperSegmentCompilerLifetime
