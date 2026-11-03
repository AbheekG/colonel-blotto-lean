import Blotto.PlayerSpecificRationalIntervals

/-! Exact sign of a raw rational polynomial at a retained algebraic root.
The actual source first computes its reduced remainder, then calls the
complete cached sign backend. No reduced-row or sign oracle is supplied. -/
namespace Blotto.PlayerSpecificPolynomialSignExecution
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificIsolationState PlayerSpecificRationalTrace PlayerSpecificSturmVariations PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (model : RationalCostModel) (m p : Data) (node : Interval) : SignType×ℕ :=
  let divided:=PlayerSpecificDivisionExecution.run p m
  let signed:=PlayerSpecificSignExecution.run model m divided.1.2 node
  (signed.1,price model divided.2+signed.2+price model (copyRow m)+price model (copyRow p)+
    price model (copyRow divided.1.2)+price model (copyRow [node.lo,node.hi])+price model [.control 1])

theorem correct (model : RationalCostModel) (m p : Data) (node : Interval) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (hv : node.lo<node.hi) (x : ℝ)
    (hu : PlayerSpecificSelectedRefinement.Unique m node x) : (run model m p node).1=sign (realEvaluate p x) := by
  have hm0 : m≠[] := by intro he; exact hirr.ne_zero (by rw [he]; rfl)
  have hr:=PlayerSpecificAlgebraicReduction.reduced m p hm hm0
  change (PlayerSpecificSignExecution.run model m (PlayerSpecificDivisionExecution.run p m).1.2 node).1=_
  rw [PlayerSpecificDivisionExecution.value,PlayerSpecificSignExecution.value]
  change PlayerSpecificAlgebraicSign.run m (reduce m p) node=sign (realEvaluate p x)
  rw [PlayerSpecificAlgebraicSign.correct m (reduce m p) node hm hirr hr hv x hu]
  rw [real_reduce m p x hu.1]

theorem candidate_correct (model : RationalCostModel) (input : Data) (hinput : semantics input≠0) (hilen : input.length≤4)
    (candidate : PlayerSpecificAlgebraicCandidates.Candidate)
    (hc : candidate∈(PlayerSpecificCandidateExecution.run model input).1) (p : Data) (x : ℝ)
    (hx : realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) :
    (run model candidate.polynomial p candidate.interval).1=sign (realEvaluate p x) := by
  have hf:=PlayerSpecificCandidateFieldInput.field_input model input hinput hilen candidate hc
  obtain ⟨y,hy,hunique⟩:=hf.2.2.2.2
  have hv : candidate.interval.lo<candidate.interval.hi := by exact_mod_cast hx.2.1.trans_le hx.2.2
  exact correct model candidate.polynomial p candidate.interval hf.1 hf.2.1 hv x
    ⟨hx.1,hx.2,fun z hz hzin => (hunique z ⟨hz,hzin⟩).trans (hunique x hx).symm⟩

end Blotto.PlayerSpecificPolynomialSignExecution
