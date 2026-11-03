import Blotto.PlayerSpecificResourceExpectation

/-! Exact real-probability semantics of the actual requested resource
pairs. This finite proof recursion is never constructed by the sampler.
All normalization promises follow from actual reached-state validity. -/
namespace Blotto.PlayerSpecificResourceIdealMean
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Normalized {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) :
    ℕ → State N → Prop
  | 0,_ => True
  | C+1,s => ∀ frame,request model p s=some frame →
      (0 ≤ realEvaluate frame.pair.probability x ∧ realEvaluate frame.pair.probability x ≤ 1) ∧
        Normalized model p x C (advance model p s frame true) ∧
        Normalized model p x C (advance model p s frame false)

theorem of_valid {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (C : ℕ) (s : State N) (hs : Valid p x s) :
    Normalized model p x C s := by
  induction C generalizing s with
  | zero => trivial
  | succ C ih =>
    intro frame hframe
    have hp := probability model p s frame hframe hc.normalized hc.irreducible hc.interval x hc.root hs
    refine ⟨?_,?_,?_⟩
    · rw [hp]
      exact ⟨(realPair model p s frame hframe x hs).probability_pos.le,(realPair model p s frame hframe x hs).probability_lt_one.le⟩
    · exact ih _ (PlayerSpecificAlgebraicResourceInvariant.advance_valid model p s frame hframe true
        hc.normalized hc.irreducible hc.interval x hc.root hs hc.lengths)
    · exact ih _ (PlayerSpecificAlgebraicResourceInvariant.advance_valid model p s frame hframe false
        hc.normalized hc.irreducible hc.interval x hc.root hs hc.lengths)

noncomputable def mean {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ)
    (f : State N → ℝ) : ℕ → State N → ℝ
  | 0,s => f s
  | C+1,s => match request model p s with
      | none => f s
      | some frame => realEvaluate frame.pair.probability x*mean model p x f C (advance model p s frame true)+
          (1-realEvaluate frame.pair.probability x)*mean model p x f C (advance model p s frame false)

theorem unit_bounds {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (f : State N → ℝ) (hf : ∀ s,0 ≤ f s ∧ f s ≤ 1) (C : ℕ) (s : State N)
    (hn : Normalized model p x C s) : 0 ≤ mean model p x f C s ∧ mean model p x f C s ≤ 1 := by
  induction C generalizing s with
  | zero => exact hf s
  | succ C ih =>
    cases he : request model p s with
    | none => simpa only [mean,he] using hf s
    | some frame =>
      have hp := hn frame he
      have hu := ih _ hp.2.1
      have hl := ih _ hp.2.2
      have hcomp : 0 ≤ 1-realEvaluate frame.pair.probability x := sub_nonneg.mpr hp.1.2
      rw [mean,he]
      constructor
      · exact add_nonneg (mul_nonneg hp.1.1 hu.1) (mul_nonneg hcomp hl.1)
      · have hU := mul_le_mul_of_nonneg_left hu.2 hp.1.1
        have hL := mul_le_mul_of_nonneg_left hl.2 hcomp
        linarith only [hU,hL]

end Blotto.PlayerSpecificResourceIdealMean
