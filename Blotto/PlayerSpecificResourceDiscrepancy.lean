import Blotto.PlayerSpecificResourceIdealMean

/-! The actual adaptive H-bit resource loop differs from its exact-
probability semantics by at most C*2^-H for every bounded future test.
Reached probabilities are derived from native state validity. -/
namespace Blotto.PlayerSpecificResourceDiscrepancy
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem under_normalized {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (H C : ℕ) (s : State N)
    (hn : PlayerSpecificResourceIdealMean.Normalized model p x C s) (f : State N → ℝ)
    (hf : ∀ t,0 ≤ f t ∧ f t ≤ 1) :
    |PlayerSpecificResourceExpectation.mean model p H C s f-PlayerSpecificResourceIdealMean.mean model p x f C s| ≤
      (C:ℝ)/(2:ℝ)^H := by
  induction C generalizing s with
  | zero => simp only [PlayerSpecificResourceExpectation.zero,PlayerSpecificResourceIdealMean.mean,sub_self,abs_zero,Nat.cast_zero,zero_div,le_refl]
  | succ C ih =>
    cases he : request model p s with
    | none =>
      rw [PlayerSpecificResourceExpectation.stopped model p H (C+1) s f he,PlayerSpecificResourceIdealMean.mean,he,sub_self,abs_zero]
      positivity
    | some frame =>
      have hp := hn frame he
      have hU := ih _ hp.2.1
      have hL := ih _ hp.2.2
      have hIU := PlayerSpecificResourceIdealMean.unit_bounds model p x f hf C _ hp.2.1
      have hIL := PlayerSpecificResourceIdealMean.unit_bounds model p x f hf C _ hp.2.2
      have hcoin := PlayerSpecificAlgebraicMidpointCoin.paper_discrepancy model p.parameters.root frame.pair.probability H
        hc.normalized hc.irreducible hc.interval x hc.root hp.1
      have h := PlayerSpecificAlgebraicCoinExpectation.mixture_error
        (PlayerSpecificAlgebraicMidpointCoin.success model p.parameters.root frame.pair.probability H)
        (realEvaluate frame.pair.probability x)
        (PlayerSpecificResourceExpectation.mean model p H C (advance model p s frame true) f)
        (PlayerSpecificResourceExpectation.mean model p H C (advance model p s frame false) f)
        (PlayerSpecificResourceIdealMean.mean model p x f C (advance model p s frame true))
        (PlayerSpecificResourceIdealMean.mean model p x f C (advance model p s frame false))
        ((C:ℝ)/(2:ℝ)^H) (1/(2:ℝ)^H)
        (PlayerSpecificAlgebraicCoinExpectation.success_bounds H
          (PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root frame.pair.probability H))
        hIU hIL hU hL hcoin
      rw [PlayerSpecificResourceExpectation.step model p H C s frame he f,PlayerSpecificResourceIdealMean.mean,he]
      calc
        _ ≤ 1/(2:ℝ)^H+(C:ℝ)/(2:ℝ)^H := h
        _ = ((C+1:ℕ):ℝ)/(2:ℝ)^H := by push_cast; ring

theorem actual_valid {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (H C : ℕ) (s : State N)
    (hs : Valid p x s) (f : State N → ℝ) (hf : ∀ t,0 ≤ f t ∧ f t ≤ 1) :
    |PlayerSpecificResourceExpectation.mean model p H C s f-PlayerSpecificResourceIdealMean.mean model p x f C s| ≤
      (C:ℝ)/(2:ℝ)^H :=
  under_normalized model p x hc H C s (PlayerSpecificResourceIdealMean.of_valid model p x hc C s hs) f hf

end Blotto.PlayerSpecificResourceDiscrepancy
