import Blotto.PlayerSpecificOutputFloorPredicateExecution
import Blotto.PlayerSpecificAlgebraicOutputFloorBounds

/-! The measured dyadic floor uses the actual one-branch lower-bound
search and exact algebraic threshold predicate, then constructs and prices
the returned rational. It has the same value and visit count as the native
floor, including zero, one and dyadic boundary points. -/
namespace Blotto.PlayerSpecificOutputFloorExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def search (root : Candidate) (a : Data) (P : ℕ) : (ℕ×ℕ)×ℕ :=
  let model:=RationalCostModel.schoolbook
  let cap:=PlayerSpecificNaturalExecution.power model 2 P
  let top:=PlayerSpecificNaturalExecution.binary model (fun x y => x+y) cap.1 1
  let found:=PlayerSpecificMeasuredCodeSearch.run model (binaryWordWidth top.1)
    (PlayerSpecificOutputFloorPredicateExecution.run root a P) 0 top.1
  (found.1,cap.2+top.2+found.2+
    price model (PlayerSpecificAlgebraicCallerFrame.run [a]
      [P,cap.1,top.1,binaryWordWidth top.1,found.1.1,found.1.2]))

theorem search_value (root : Candidate) (a : Data) (P : ℕ) :
    (search root a P).1=PlayerSpecificAlgebraicOutputFloor.search root a P := by
  simp only [search,PlayerSpecificNaturalExecution.power_value,
    PlayerSpecificNaturalExecution.binary_value,
    PlayerSpecificMeasuredCodeSearch.value,
    PlayerSpecificOutputFloorPredicateExecution.value,
    PlayerSpecificAlgebraicOutputFloor.search,MonotoneCodeSearch.first]

def round (root : Candidate) (a : Data) (P : ℕ) : ℚ×ℕ :=
  let model:=RationalCostModel.schoolbook
  let found:=search root a P
  let denominator:=PlayerSpecificNaturalExecution.power model 2 P
  let value:ℚ:=(found.1.1:ℚ)/(denominator.1:ℚ)
  let divided:=GeneralPaperRationalPrimitivePrice.binary model.rat
    (fun u v => u/v) (found.1.1:ℚ) (denominator.1:ℚ)
  (value,found.2+denominator.2+divided+
    price model (PlayerSpecificAlgebraicCallerFrame.run
      [root.polynomial,[root.interval.lo,root.interval.hi],a,[value]]
      [P,found.1.1,found.1.2,denominator.1]))

theorem round_value (root : Candidate) (a : Data) (P : ℕ) :
    (round root a P).1=PlayerSpecificAlgebraicOutputFloor.round root a P := by
  simp only [round,search_value,PlayerSpecificNaturalExecution.power_value,
    PlayerSpecificAlgebraicOutputFloor.round,Nat.cast_pow,Nat.cast_ofNat]

theorem visits (root : Candidate) (a : Data) (P : ℕ) :
    (search root a P).1.2≤P+2 := by
  rw [search_value]
  exact PlayerSpecificAlgebraicOutputFloorBounds.visits root a P

end Blotto.PlayerSpecificOutputFloorExecution
