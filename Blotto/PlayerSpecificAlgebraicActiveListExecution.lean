import Blotto.PlayerSpecificAlgebraicComparisonCost

/-! Executed active-list filtering. The cached test result is reused for
the retained list; source prices include row reads, list copies, index,
length, comparison and return-control words on each recursive caller. -/
namespace Blotto.PlayerSpecificAlgebraicActiveListExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {N : ℕ} (length resource : Data) (j : Fin N) (ids result : List (Fin N)) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [length,resource]
    ([N,j.val,ids.length,result.length]++ids.map Fin.val++result.map Fin.val)

def run {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths resources : FixedArrayTable N Data) :
    List (Fin N) → List (Fin N)×ℕ
  | [] => ([],price model (PlayerSpecificAlgebraicCallerFrame.run [] [N,0]))
  | j::ids =>
      let tested:=PlayerSpecificAlgebraicComparisonExecution.active model root (lengths.read j) (resources.read j)
      let tail:=run model root lengths resources ids
      let result:=if tested.1 then j::tail.1 else tail.1
      (result,tested.2+tail.2+price model (frame (lengths.read j) (resources.read j) j (j::ids) result))

theorem value {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths resources : FixedArrayTable N Data)
    (ids : List (Fin N)) :
    (run model root lengths resources ids).1=ids.filter
      (fun j => PlayerSpecificAlgebraicActive.run model root (lengths.read j) (resources.read j)) := by
  induction ids with
  | nil => rfl
  | cons j ids ih =>
    simp only [run,ih,PlayerSpecificAlgebraicComparisonExecution.active_value,List.filter_cons]

theorem length {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths resources : FixedArrayTable N Data)
    (ids : List (Fin N)) : (run model root lengths resources ids).1.length ≤ ids.length := by
  rw [value]
  exact List.length_filter_le _ _

end Blotto.PlayerSpecificAlgebraicActiveListExecution
