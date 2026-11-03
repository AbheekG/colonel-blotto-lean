import Blotto.PlayerSpecificUniformItemsCost

/-! Measured cached greedy grouping. Each combined total and fit test
is computed once; the chosen tail and completed group rows are retained.
Input/output members, coefficient rows, indices and controls are priced. -/
namespace Blotto.PlayerSpecificAlgebraicGroupingExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {N : ℕ} (root : Candidate) (B : ℚ) (current : List (Fin N)) (s combined : Data)
    (rest : List (Fin N)) (result : List (Group N)) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([root.polynomial,[root.interval.lo,root.interval.hi,B],s,combined]++result.map Group.total)
    ([N,current.length,rest.length,result.length,1]++current.map Fin.val++rest.map Fin.val++
      result.flatMap (fun g => g.members.map Fin.val))

def packAux {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ) :
    List (Fin N) → Data → List (Fin N) → List (Group N)×ℕ
  | current,s,[] =>
      let result:=[⟨current.reverse,s⟩]
      (result,price model (frame root B current s [] [] result))
  | current,s,k::rest =>
      let combined:=PlayerSpecificFieldCombination.run false root.polynomial s (lengths.read k)
      let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root combined.1 [B]
      if tested.1 then
        let tail:=packAux model root lengths B (k::current) combined.1 rest
        (tail.1,price model combined.2+tested.2+tail.2+price model (frame root B current s combined.1 (k::rest) tail.1))
      else
        let tail:=packAux model root lengths B [k] (lengths.read k) rest
        let result:List (Group N):=⟨current.reverse,s⟩::tail.1
        (result,price model combined.2+tested.2+tail.2+price model (frame root B current s combined.1 (k::rest) result))

theorem aux_value {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (current : List (Fin N)) (s : Data) (rest : List (Fin N)) :
    (packAux model root lengths B current s rest).1=PlayerSpecificAlgebraicGrouping.packAux model root lengths.read B current s rest := by
  induction rest generalizing current s with
  | nil => rfl
  | cons k rest ih =>
    simp only [packAux,PlayerSpecificFieldCombination.value,PlayerSpecificAlgebraicComparisonExecution.value,
      Bool.false_eq_true,ite_false,PlayerSpecificAlgebraicGrouping.packAux]
    split <;> simp_all only

def run {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ) :
    List (Fin N) → List (Group N)×ℕ
  | [] => ([],price model (frame (N:=N) root B [] [] [] [] []))
  | k::rest =>
      let result:=packAux model root lengths B [k] (lengths.read k) rest
      (result.1,result.2+price model (frame root B [k] (lengths.read k) [] rest result.1))

theorem value {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (items : List (Fin N)) : (run model root lengths B items).1=PlayerSpecificAlgebraicGrouping.run model root lengths.read B items := by
  cases items <;> simp only [run,PlayerSpecificAlgebraicGrouping.run,aux_value]

end Blotto.PlayerSpecificAlgebraicGroupingExecution
