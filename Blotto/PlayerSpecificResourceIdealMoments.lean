import Blotto.PlayerSpecificResourceIdealLaw

/-! Exact resource choices preserve every reached coordinate mean.
Hence every affine terminal marginal formula averages to its original
coefficient, for the actual maintained-pair selector and state updates. -/
namespace Blotto.PlayerSpecificResourceIdealMoments
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem step {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (s : State N) (hs : Valid p x s)
    (frame : Frame N) (hf : request model p s=some frame) (j : Fin N) :
    realEvaluate frame.pair.probability x*eval (advance model p s frame true) x j+
      (1-realEvaluate frame.pair.probability x)*eval (advance model p s frame false) x j=eval s x j := by
  have hij := distinct model p s frame hf x hs
  have hfrac := fractional model p s frame hf x hs
  have hpair := (fields model p s frame hf).2
  have hu : realEvaluate frame.pair.upperA x=(realPair model p s frame hf x hs).upper := by
    have h := PlayerSpecificAlgebraicPairValues.upper model p.parameters.root (p.rows.read frame.first).length
      (p.rows.read frame.second).length (s.data.read frame.first) (s.data.read frame.second)
      hc.normalized hc.irreducible hc.interval x hc.root
    simpa only [hpair,realPair,resourcePair,RoundingPair.upper,RoundingPair.total,lengths,eval] using h
  have hl : realEvaluate frame.pair.lowerA x=(realPair model p s frame hf x hs).lower := by
    have h := PlayerSpecificAlgebraicPairValues.lower model p.parameters.root (p.rows.read frame.first).length
      (p.rows.read frame.second).length (s.data.read frame.first) (s.data.read frame.second)
      hc.normalized hc.irreducible hc.interval x hc.root
    simpa only [hpair,realPair,resourcePair,RoundingPair.lower,RoundingPair.total,lengths,eval] using h
  rw [probability model p s frame hf hc.normalized hc.irreducible hc.interval x hc.root hs,
    advance_eval model p s frame hf hij true x hc.root.1,
    advance_eval model p s frame hf hij false x hc.root.1]
  simp only [ite_true,Bool.false_eq_true,ite_false,hu,hl]
  exact updatePair_expectation (lengths p x) (eval s x) hij hfrac.1 hfrac.2 j

theorem affine {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (C : ℕ) (s : State N) (hs : Valid p x s)
    (a b : ℝ) (j : Fin N) :
    PlayerSpecificResourceIdealMean.mean model p x (fun t => a+b*eval t x j) C s=a+b*eval s x j := by
  induction C generalizing s with
  | zero => rfl
  | succ C ih =>
    cases he : request model p s with
    | none => simp only [PlayerSpecificResourceIdealMean.mean,he]
    | some frame =>
      have hu := PlayerSpecificAlgebraicResourceInvariant.advance_valid model p s frame he true
        hc.normalized hc.irreducible hc.interval x hc.root hs hc.lengths
      have hl := PlayerSpecificAlgebraicResourceInvariant.advance_valid model p s frame he false
        hc.normalized hc.irreducible hc.interval x hc.root hs hc.lengths
      simp only [PlayerSpecificResourceIdealMean.mean,he]
      rw [ih _ hu,ih _ hl]
      calc
        _ = a+b*(realEvaluate frame.pair.probability x*eval (advance model p s frame true) x j+
          (1-realEvaluate frame.pair.probability x)*eval (advance model p s frame false) x j) := by ring
        _ = _ := by rw [step model p x hc s hs frame he j]

end Blotto.PlayerSpecificResourceIdealMoments
