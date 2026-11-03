import Blotto.PlayerSpecificAlgebraicCellTests

/-! Actual exact interior-candidate acceptance uses the computed algebraic
sign backend on five fixed-degree rational polynomials. Every real test is
proved equivalent to the preserved interval and endpoint gates. -/
namespace Blotto.PlayerSpecificAlgebraicCandidateTest
open SignType PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicCellTests
set_option autoImplicit false
set_option maxHeartbeats 2500000

def nonnegative (s : SignType) : Bool := decide (s≠.neg)
def upperTest (model : RationalCostModel) (candidate : Candidate) (bound : Option ℚ) : Bool :=
  match bound with
  | none => true
  | some q => decide ((PlayerSpecificPolynomialSignExecution.run model candidate.polynomial (upper q) candidate.interval).1=.pos)
def run (model : RationalCostModel) (c : Cell) (candidate : Candidate) : Bool :=
  decide ((PlayerSpecificPolynomialSignExecution.run model candidate.polynomial positive candidate.interval).1=.pos) &&
  decide ((PlayerSpecificPolynomialSignExecution.run model candidate.polynomial (lower c) candidate.interval).1=.pos) &&
  upperTest model candidate c.upper &&
  nonnegative (PlayerSpecificPolynomialSignExecution.run model candidate.polynomial (firstGate c) candidate.interval).1 &&
  nonnegative (PlayerSpecificPolynomialSignExecution.run model candidate.polynomial (secondGate c) candidate.interval).1

theorem nonnegative_sign (x : ℝ) : nonnegative (sign x)=true ↔ 0≤x := by
  simp only [nonnegative,decide_eq_true_eq,SignType.neg_eq_neg_one,ne_eq,sign_eq_neg_one_iff,not_lt]

theorem correct (model : RationalCostModel) (input : Data) (hinput : semantics input≠0) (hilen : input.length≤4)
    (candidate : Candidate) (hc : candidate∈(PlayerSpecificCandidateExecution.run model input).1)
    (c : Cell) (b : ℚ) (hb : b≠0) (x : ℝ)
    (hx : realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) :
    run model c candidate=true ↔ PlayerSpecificCellCandidates.Interior (castCell c) x ∧
      PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) x := by
  have hpositive:=PlayerSpecificPolynomialSignExecution.candidate_correct model input hinput hilen candidate hc positive x hx
  have hlower:=PlayerSpecificPolynomialSignExecution.candidate_correct model input hinput hilen candidate hc (lower c) x hx
  have hfirst:=PlayerSpecificPolynomialSignExecution.candidate_correct model input hinput hilen candidate hc (firstGate c) x hx
  have hsecond:=PlayerSpecificPolynomialSignExecution.candidate_correct model input hinput hilen candidate hc (secondGate c) x hx
  have hu : upperTest model candidate c.upper=true ↔
      match (castCell c).upper with | none => True | some q => x<q := by
    cases he : c.upper with
    | none => simp only [upperTest,castCell,he,Option.map_none]
    | some q =>
      have hupper:=PlayerSpecificPolynomialSignExecution.candidate_correct model input hinput hilen candidate hc (upper q) x hx
      simp only [upperTest,castCell,he,Option.map_some,decide_eq_true_eq,hupper,upper_value,
        SignType.pos_eq_one,sign_eq_one_iff,sub_pos]
  rw [run]
  simp only [Bool.and_eq_true,decide_eq_true_eq,hpositive,hlower,hfirst,hsecond,positive_value,lower_value,
    SignType.pos_eq_one,sign_eq_one_iff,sub_pos,nonnegative_sign,hu]
  rw [←gates_iff c b hb x]
  simp only [PlayerSpecificCellCandidates.Interior,castCell]
  tauto

end Blotto.PlayerSpecificAlgebraicCandidateTest
