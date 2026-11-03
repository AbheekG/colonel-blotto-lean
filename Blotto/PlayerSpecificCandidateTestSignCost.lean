import Blotto.PlayerSpecificCandidateTestCopyCost

/-! Each actual acceptance comparison has a complete original-cell and
selected-root source bound, including the optional upper comparison. -/
namespace Blotto.PlayerSpecificCandidateTestSignCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificIsolationState PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificCandidateTestExecution PlayerSpecificCandidateTestBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem sign_cost (model : RationalCostModel) (candidate : Candidate) (p : Data) (H T : ℕ)
    (hm : HasHeight candidate.polynomial T) (he : HasHeight [candidate.interval.lo,candidate.interval.hi] T)
    (hn : Normalized candidate.polynomial) (hm0 : candidate.polynomial≠[]) (hml : candidate.polynomial.length≤4)
    (hp : Bounded p (4*H+4)) (hv : candidate.interval.lo<candidate.interval.hi) :
    (PlayerSpecificPolynomialSignExecution.run model candidate.polynomial p candidate.interval).2≤
      signWorkCoefficient*size H T*model.rat (width H T) := by
  have hT : T≤operandHeight H T := by unfold operandHeight; omega
  have hP : 4*H+4≤operandHeight H T := by unfold operandHeight; omega
  have hi:=encoded_input candidate.polynomial p candidate.interval (operandHeight H T)
    (mono hm hT) (mono hp.1 hP) (mono he hT) hml hp.2
  have hc:=PlayerSpecificPolynomialSignCost.run_cost model candidate.polynomial p candidate.interval hn hm0 hml hp.2 hv
  have hw:=sign_work_profile PlayerSpecificPolynomialSignCost.workCoefficient _ (operandHeight H T) hi
  exact hc.trans (Nat.mul_le_mul hw (model.monotone (sign_width H T _ hi)))

theorem upper_cost (model : RationalCostModel) (candidate : Candidate) (row : Option Data) (H T : ℕ)
    (hm : HasHeight candidate.polynomial T) (he : HasHeight [candidate.interval.lo,candidate.interval.hi] T)
    (hn : Normalized candidate.polynomial) (hm0 : candidate.polynomial≠[]) (hml : candidate.polynomial.length≤4)
    (hp : ∀ p∈row,Bounded p (4*H+4)) (hv : candidate.interval.lo<candidate.interval.hi) :
    (upperRun model candidate row).2≤
      signWorkCoefficient*size H T*model.rat (width H T)+6*model.rat (width H T) := by
  cases row with
  | none =>
    have hc:=PlayerSpecificCandidateTestCopyCost.controls model H T [0] (by simp)
    change price model [.control 0]≤3*model.rat (width H T) at hc
    exact hc.trans (by omega)
  | some p =>
    have hs:=sign_cost model candidate p H T hm he hn hm0 hml (hp p (Option.mem_some_self p)) hv
    have hc:=PlayerSpecificCandidateTestCopyCost.controls model H T
      [signWord (PlayerSpecificPolynomialSignExecution.run model candidate.polynomial p candidate.interval).1,1] (by
        intro n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
        rcases hn with rfl|rfl
        · exact (PlayerSpecificCandidateTestCopyCost.sign_word _).trans (by decide)
        · decide)
    change price model [.control (signWord (PlayerSpecificPolynomialSignExecution.run model candidate.polynomial p candidate.interval).1),.control 1]≤
      6*model.rat (width H T) at hc
    exact Nat.add_le_add hs hc

end Blotto.PlayerSpecificCandidateTestSignCost
