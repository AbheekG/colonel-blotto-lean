import Blotto.PlayerSpecificSignExecutionCost

/-! Exact selected-root sign and complete polynomial bit cost on one
actual cached return, with all analysis sizes derived from encoded inputs. -/
namespace Blotto.PlayerSpecificSignContract
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificIsolationState
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

def widthCoefficient : ℕ := 100000*(PlayerSpecificSignPreparationBudget.coefficient+1)
def workCoefficient : ℕ := 21000000000*(PlayerSpecificSignPreparationBudget.coefficient+1)
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem height_profile (K H : ℕ) : K*(H+1)+1≤(K+1)*(H+1) := by nlinarith
theorem width_profile (K H : ℕ) : 100000*(K*(H+1)+1)≤(100000*(K+1))*(H+1) := by
  have h:=Nat.mul_le_mul_left 100000 (height_profile K H)
  simpa only [mul_assoc] using h

theorem source_cost (model : RationalCostModel) (m a : Data) (node : Interval)
    (hml : m.length≤4) (hal : a.length≤3) (hv : node.lo<node.hi) :
    (PlayerSpecificSignExecution.run model m a node).2≤
      workCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1)*
        model.rat (widthCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hc:=PlayerSpecificSignExecutionCost.run_cost model m a node hml hal hv
  have hh:=height_profile PlayerSpecificSignPreparationBudget.coefficient H
  have hw:=width_profile PlayerSpecificSignPreparationBudget.coefficient H
  change PlayerSpecificSignPreparationBudget.width H≤widthCoefficient*(H+1) at hw
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul_left 21000000000 hh) (model.monotone hw)
  exact hc.trans (hm.trans_eq (by unfold workCoefficient; ring))

theorem actual_contract (model : RationalCostModel) (m a : Data) (node : Interval)
    (hm : Normalized m) (hirr : Irreducible (semantics m)) (hml : m.length≤4)
    (ha : Reduced m a) (hv : node.lo<node.hi) (x : ℝ) (hu : PlayerSpecificSelectedRefinement.Unique m node x) :
    let result:=PlayerSpecificSignExecution.run model m a node
    result.1=sign (realEvaluate a x) ∧
      result.2≤workCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1)*
        model.rat (widthCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1)) := by
  have hal : a.length≤3 := by have hl:=ha.2; omega
  refine ⟨?_,source_cost model m a node hml hal hv⟩
  rw [PlayerSpecificSignExecution.value]
  exact PlayerSpecificAlgebraicSign.correct m a node hm hirr ha hv x hu

theorem polynomial_cost (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) (hv : node.lo<node.hi) :
    (PlayerSpecificSignExecution.run RationalCostModel.schoolbook m a node).2≤
      polynomialCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1)^3 := by
  have hc:=source_cost RationalCostModel.schoolbook m a node hml hal hv
  change (PlayerSpecificSignExecution.run RationalCostModel.schoolbook m a node).2≤
    workCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1)*
      ((widthCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1))*
        (widthCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1))+
          widthCoefficient*(PlayerSpecificSignLinearSizes.inputHeight m a node+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

theorem candidate_contract (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : PlayerSpecificAlgebraicCandidates.Candidate)
    (hc : candidate∈(PlayerSpecificCandidateExecution.run model p).1)
    (a : Data) (ha : Reduced candidate.polynomial a) (x : ℝ)
    (hx : realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) :
    let result:=PlayerSpecificSignExecution.run model candidate.polynomial a candidate.interval
    result.1=sign (realEvaluate a x) ∧
      result.2≤workCoefficient*(PlayerSpecificSignLinearSizes.inputHeight candidate.polynomial a candidate.interval+1)*
        model.rat (widthCoefficient*(PlayerSpecificSignLinearSizes.inputHeight candidate.polynomial a candidate.interval+1)) := by
  have hf:=PlayerSpecificCandidateFieldInput.field_input model p hp hlen candidate hc
  have hal : a.length≤3 := by have hl:=ha.2; have hm:=hf.2.2.1; omega
  have hv : candidate.interval.lo<candidate.interval.hi := by exact_mod_cast hx.2.1.trans_le hx.2.2
  refine ⟨?_,source_cost model candidate.polynomial a candidate.interval hf.2.2.1 hal hv⟩
  rw [PlayerSpecificSignExecution.value]
  exact PlayerSpecificCandidateSign.correct model p hp hlen candidate hc a ha x hx

end Blotto.PlayerSpecificSignContract
