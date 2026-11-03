import Blotto.PlayerSpecificCandidateTestBudget

/-! Candidate caller copies and all sign/Boolean/optional tags use their
actual bounded words. No unpriced record return is left at this caller. -/
namespace Blotto.PlayerSpecificCandidateTestCopyCost
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicCandidates PlayerSpecificCandidateTestExecution PlayerSpecificCandidateTestBudget
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem sign_word (s : SignType) : signWord s≤2 := by cases s <;> decide
theorem bool_word (b : Bool) : (if b then 1 else 0 : ℕ)≤1 := by cases b <;> decide

theorem controls (model : RationalCostModel) (H T : ℕ) (words : List ℕ) (h : ∀ n∈words,n≤5) :
    price model (words.map Event.control)≤3*words.length*model.rat (width H T) := by
  have hw:=width_large H T
  have hf : Fits (width H T) (words.map Event.control) := by
    intro e he
    obtain ⟨n,hn,rfl⟩:=List.mem_map.mp he
    exact (PlayerSpecificRationalTrace.control_width n).trans (by have hh:=h n hn; omega)
  simpa only [List.length_map] using price_bound model (width H T) (by omega) _ hf

theorem frame_cost (model : RationalCostModel) (candidate : Candidate) (H T : ℕ)
    (hm : HasHeight candidate.polynomial T) (hml : candidate.polynomial.length≤4)
    (he : HasHeight [candidate.interval.lo,candidate.interval.hi] T)
    (a b d e : SignType) (upper accepted : Bool) :
    price model (frame candidate a b d e upper accepted)≤153*model.rat (width H T) := by
  have hw:=width_large H T
  have hT : T≤operandHeight H T := by unfold operandHeight; omega
  have hp:=PlayerSpecificExtendedCopyCost.row_cost model candidate.polynomial (operandHeight H T) (width H T)
    (mono hm hT) (by omega) hw.2.1 hw.2.2
  have he:=PlayerSpecificExtendedCopyCost.row_cost model [candidate.interval.lo,candidate.interval.hi]
    (operandHeight H T) (width H T) (mono he hT) (by simp) hw.2.1 hw.2.2
  have ht:=controls model H T [signWord a,signWord b,signWord d,signWord e,
    if upper then 1 else 0,if accepted then 1 else 0,5] (by
      intro n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact (sign_word a).trans (by decide)
      · exact (sign_word b).trans (by decide)
      · exact (sign_word d).trans (by decide)
      · exact (sign_word e).trans (by decide)
      · exact (bool_word upper).trans (by decide)
      · exact (bool_word accepted).trans (by decide)
      · decide)
  change price model [.control (signWord a),.control (signWord b),.control (signWord d),.control (signWord e),
    .control (if upper then 1 else 0),.control (if accepted then 1 else 0),.control 5]≤21*model.rat (width H T) at ht
  simp only [frame,price_append]
  nlinarith only [hp,he,ht]

end Blotto.PlayerSpecificCandidateTestCopyCost
