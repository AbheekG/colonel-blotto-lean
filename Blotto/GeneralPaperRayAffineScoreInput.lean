import Blotto.GeneralPaperRayParametricStage

/-! Construct the affine input fields from the reused actual score matrix
and literal rational ray anchors. The initial DP stores exactly score zero.
No minimum/predecessor or affine-cost oracle is supplied.
-/
namespace Blotto.GeneralPaperRayAffineScoreInput
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
set_option autoImplicit false
set_option maxHeartbeats 3500000

def fields {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) : List (Field K) :=
  List.ofFn (fun j => FixedArrayTable.ofFn (fun l =>
    (GeneralPaperRayQueryWork.scores matrix j l,
      Affine.mk (GeneralPaperRayAnchorCosts.anchorQ x j l) (GeneralPaperRayAnchorCosts.anchorQ w j l))))

theorem fields_length {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) : (fields matrix x w).length=m := by simp only [fields,List.length_ofFn]

theorem fields_data {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (t : ℚ) :
    (fields matrix x w).map (fun field => fieldAt field t)=
      GeneralPaperExactScoreDP.fields (GeneralPaperRayQueryWork.scores matrix) (GeneralPaperRayAnchorCosts.costs x w t) := by
  simp only [fields,List.map_ofFn,fieldAt,GeneralPaperExactScoreDP.fields]
  apply congrArg List.ofFn
  funext j
  apply congrArg FixedArrayTable.ofFn
  funext l
  simp only [FixedArrayTable.read_ofFn,GeneralPaperRayAnchorCosts.costs,Affine.value,mul_comm]

def initial (S K : ℕ) : Table S K :=
  FixedArrayTable.ofFn (fun s => if s.val=0 then some ⟨⟨0,0⟩,[]⟩ else none)

theorem initial_data (S K : ℕ) (t : ℚ) (s : Fin (S+1)) :
    ((tableAt (initial S K) t).read s)=(GeneralPaperExactScoreDP.run (K := K) S []).read s := by
  simp only [tableAt,initial,FixedArrayTable.read_ofFn,GeneralPaperExactScoreDP.run]
  split
  · simp only [Option.map_some,Choice.atPoint,Affine.value,zero_mul,add_zero]
  · rfl

end Blotto.GeneralPaperRayAffineScoreInput
