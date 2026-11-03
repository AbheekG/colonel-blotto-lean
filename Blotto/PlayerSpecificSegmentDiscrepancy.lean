import Blotto.PlayerSpecificSegmentExpectation

/-! Actual sequential algebraic segment coins accumulate at most one
2^-H error per visited slot. Remaining mass and zero divisions follow
the executing cached subtraction program exactly. -/
namespace Blotto.PlayerSpecificSegmentDiscrepancy
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem normalized {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (items : List (Fin slots)) (remaining : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (hr : Reduced root.polynomial remaining)
    (hn : PlayerSpecificSegmentIdealMean.Remaining (fun j => realEvaluate (weights.read j) x) items (realEvaluate remaining x))
    (f : Fin slots → ℝ) (hf : ∀ j,0 ≤ f j ∧ f j ≤ 1) :
    |PlayerSpecificSegmentExpectation.mean model root weights fallback H items remaining f-
      PlayerSpecificSegmentIdealMean.mean (fun j => realEvaluate (weights.read j) x) fallback f items (realEvaluate remaining x)| ≤
        (items.length:ℝ)/(2:ℝ)^H := by
  let w := fun j => realEvaluate (weights.read j) x
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  induction items generalizing remaining with
  | nil => simp only [PlayerSpecificSegmentExpectation.nil,PlayerSpecificSegmentIdealMean.mean,sub_self,abs_zero,List.length_nil,Nat.cast_zero,zero_div,le_refl]
  | cons slot rest ih =>
    have hb := PlayerSpecificSegmentIdealMean.head_bounds w slot rest (realEvaluate remaining x) hn
    have hp := PlayerSpecificSegmentIdealMean.probability_bounds w slot rest (realEvaluate remaining x) hn
    let next := PlayerSpecificAlgebraicField.minus root.polynomial remaining (weights.read slot)
    let probability := PlayerSpecificAlgebraicField.divide root.polynomial (weights.read slot) remaining
    have hnext : realEvaluate next x=realEvaluate remaining x-w slot := PlayerSpecificAlgebraicField.minus_value _ _ _ x hx.1
    have hnr : Reduced root.polynomial next := PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0
    have hnt : PlayerSpecificSegmentIdealMean.Remaining w rest (realEvaluate next x) := by
      rw [hnext]
      exact hb.2.2
    have ht := ih next hnr hnt
    rw [hnext] at ht
    have hu := PlayerSpecificSegmentIdealMean.unit_bounds w fallback f hf rest (realEvaluate remaining x-w slot) hb.2.2
    have hprob : realEvaluate probability x=w slot/realEvaluate remaining x :=
      PlayerSpecificAlgebraicField.divide_value _ _ _ hm hirr hr x hx.1
    have hprobBounds : 0 ≤ realEvaluate probability x ∧ realEvaluate probability x ≤ 1 := by rw [hprob]; exact hp
    have hcoin := PlayerSpecificAlgebraicMidpointCoin.paper_discrepancy model root probability H hm hirr hv x hx hprobBounds
    rw [hprob] at hcoin
    have htrue : |f slot-f slot| ≤ (rest.length:ℝ)/(2:ℝ)^H := by rw [sub_self,abs_zero]; positivity
    have h := PlayerSpecificAlgebraicCoinExpectation.mixture_error
      (PlayerSpecificAlgebraicMidpointCoin.success model root probability H) (w slot/realEvaluate remaining x)
      (f slot) (PlayerSpecificSegmentExpectation.mean model root weights fallback H rest next f)
      (f slot) (PlayerSpecificSegmentIdealMean.mean w fallback f rest (realEvaluate remaining x-w slot))
      ((rest.length:ℝ)/(2:ℝ)^H) (1/(2:ℝ)^H)
      (PlayerSpecificAlgebraicCoinExpectation.success_bounds H (PlayerSpecificAlgebraicMidpointCoin.run model root probability H))
      (hf slot) hu htrue ht hcoin
    rw [PlayerSpecificSegmentExpectation.step,PlayerSpecificSegmentIdealMean.mean]
    calc
      _ ≤ 1/(2:ℝ)^H+(rest.length:ℝ)/(2:ℝ)^H := h
      _ = ((slot::rest).length:ℝ)/(2:ℝ)^H := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

end Blotto.PlayerSpecificSegmentDiscrepancy
