import Blotto.PlayerSpecificCandidateLookup

/-! An executing candidate selector retains the actual original interval
and copies every input and returned defining-polynomial record. -/
namespace Blotto.PlayerSpecificCandidateSelection
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificIsolationState PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2000000

def copyCandidate (candidate : Candidate) : Trace :=
  copyRow candidate.polynomial++PlayerSpecificSplitExecution.copyInterval candidate.interval

def run (model : RationalCostModel) (factors residual : Data) (node : Interval) : Candidate×ℕ :=
  let found:=PlayerSpecificCandidateLookup.run model factors node
  let chosen:=match found.1 with
    | none => (residual,copyRow residual)
    | some q => PlayerSpecificLinearFactorExecution.run q
  let candidate:Candidate:=⟨chosen.1,node⟩
  (candidate,found.2+price model chosen.2+price model (copyRow factors)+price model (copyRow residual)+
    price model (copyCandidate candidate)+price model [.control 2])

theorem value (model : RationalCostModel) (factors residual : Data) (node : Interval) :
    (run model factors residual node).1=select factors residual node := by
  rw [run,select]
  simp only [PlayerSpecificCandidateLookup.value]
  cases lookup factors node <;> simp only [PlayerSpecificLinearFactorExecution.value]

theorem bounds (model : RationalCostModel) (factors residual : Data) (node : Interval) (H : ℕ)
    (hf : HasHeight factors H) (hr : HasHeight residual H) (hrl : residual.length≤4) (hH : 1≤H) :
    HasHeight (run model factors residual node).1.polynomial H ∧
      (run model factors residual node).1.polynomial.length≤4 ∧
      (run model factors residual node).1.interval=node := by
  rw [value]
  cases he : lookup factors node with
  | none =>
    simp only [select,he]
    exact ⟨hr,hrl,True.intro⟩
  | some q =>
    have hq:=(lookup_some factors node q he).1
    simp only [select,he]
    exact ⟨PlayerSpecificFactorHeights.linear_height q H (hf q hq) hH,by
      simp only [PlayerSpecificLinearFactor.linear,List.length_cons,List.length_nil]; decide,True.intro⟩

theorem copy_cost (model : RationalCostModel) (candidate : Candidate) (H W : ℕ)
    (hp : HasHeight candidate.polynomial H) (hlen : candidate.polynomial.length≤4)
    (hlo : RationalHeight candidate.interval.lo H) (hhi : RationalHeight candidate.interval.hi H)
    (hl : candidate.interval.loValue≤5) (hh : candidate.interval.hiValue≤5)
    (hHW : 1+2*H≤W) (hW : 32≤W) : price model (copyCandidate candidate)≤81*model.rat W := by
  have hr:=PlayerSpecificExtendedCopyCost.row_cost model candidate.polynomial H W hp (by omega) hHW hW
  have hn:=PlayerSpecificSplitTraceCost.copyInterval_cost model candidate.interval H W hlo hhi hl hh hHW (by omega)
  rw [copyCandidate,price_append]
  omega

theorem run_cost (model : RationalCostModel) (factors residual : Data) (node : Interval) (H W : ℕ)
    (hf : HasHeight factors H) (hr : HasHeight residual H) (hfl : factors.length≤3) (hrl : residual.length≤4)
    (hlo : RationalHeight node.lo H) (hhi : RationalHeight node.hi H)
    (hl : node.loValue≤5) (hh : node.hiValue≤5) (hH : 1≤H)
    (hHW : 8*H+32≤W) : (run model factors residual node).2≤2000*model.rat W := by
  have hW : 32≤W := by omega
  have hHW' : 1+2*H≤W := by omega
  have hfcopy:=PlayerSpecificExtendedCopyCost.row_cost model factors H W hf (by omega) hHW' hW
  have hrcopy:=PlayerSpecificExtendedCopyCost.row_cost model residual H W hr (by omega) hHW' hW
  have hlookup:=PlayerSpecificCandidateLookup.run_cost model factors node H W hf hfl hlo hhi hl hh hHW' hW
  have hlprice : (PlayerSpecificCandidateLookup.run model factors node).2≤800*model.rat W := by
    have hm:=Nat.mul_le_mul_right (200*model.rat W) (show factors.length+1≤4 by omega)
    nlinarith only [hlookup,hm]
  have hb:=bounds model factors residual node H hf hr hrl hH
  have houtput:=copy_cost model (run model factors residual node).1 H W hb.1 hb.2.1
    (by rw [hb.2.2]; exact hlo) (by rw [hb.2.2]; exact hhi)
    (by rw [hb.2.2]; exact hl) (by rw [hb.2.2]; exact hh) hHW' hW
  have hc:=event_price model W (by omega) (.control 2) ((control_width 2).trans (by omega))
  change price model [.control 2]≤3*model.rat W at hc
  cases he : (PlayerSpecificCandidateLookup.run model factors node).1 with
  | none =>
    simp only [run,he] at houtput ⊢
    nlinarith only [hlprice,hrcopy,hfcopy,houtput,hc]
  | some q =>
    have hq:=(lookup_some factors node q ((PlayerSpecificCandidateLookup.value model factors node).symm.trans he)).1
    have hlinear:=PlayerSpecificLinearFactorExecution.run_cost model q H (hf q hq) hH
    have hlp:=hlinear.trans (Nat.mul_le_mul_left 60 (model.monotone (by omega : 8*H+16≤W)))
    simp only [run,he] at houtput ⊢
    nlinarith only [hlprice,hlp,hrcopy,hfcopy,houtput,hc]

end Blotto.PlayerSpecificCandidateSelection
