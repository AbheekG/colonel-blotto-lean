import Blotto.PlayerSpecificAlgebraicSign

/-! Exact sign is connected to an actual computed candidate. The defining
polynomial, normalized basis and selected conjugate are derived from that
same root-preparation return, not supplied as a numerical sign/root oracle. -/
namespace Blotto.PlayerSpecificCandidateSign
open SignType PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 1500000

def run (candidate : Candidate) (a : Data) : SignType :=
  PlayerSpecificAlgebraicSign.run candidate.polynomial a candidate.interval

theorem correct (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : Candidate) (hc : candidate∈(PlayerSpecificCandidateExecution.run model p).1)
    (a : Data) (ha : Reduced candidate.polynomial a) (x : ℝ)
    (hx : realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) :
    run candidate a=sign (realEvaluate a x) := by
  have hf:=PlayerSpecificCandidateFieldInput.field_input model p hp hlen candidate hc
  obtain ⟨y,hy,hunique⟩:=hf.2.2.2.2
  have hu : PlayerSpecificSelectedRefinement.Unique candidate.polynomial candidate.interval x :=
    ⟨hx.1,hx.2,fun z hz hzin => (hunique z ⟨hz,hzin⟩).trans (hunique x hx).symm⟩
  have hv : candidate.interval.lo<candidate.interval.hi := by
    have hh:=hx.2.1.trans_le hx.2.2
    exact_mod_cast hh
  exact PlayerSpecificAlgebraicSign.correct candidate.polynomial a candidate.interval hf.1 hf.2.1 ha hv x hu

theorem actual_contract (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : Candidate) (hc : candidate∈(PlayerSpecificCandidateExecution.run model p).1)
    (a : Data) (ha : Reduced candidate.polynomial a) :
    ∃! x : ℝ,realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x ∧
      run candidate a=sign (realEvaluate a x) := by
  have hf:=PlayerSpecificCandidateFieldInput.field_input model p hp hlen candidate hc
  obtain ⟨x,hx,hunique⟩:=hf.2.2.2.2
  exact ⟨x,⟨hx.1,hx.2,correct model p hp hlen candidate hc a ha x hx⟩,
    fun y hy => hunique y ⟨hy.1,hy.2.1⟩⟩

end Blotto.PlayerSpecificCandidateSign
