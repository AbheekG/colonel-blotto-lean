import Blotto.GeneralPaperRayFixedQuerySize

/-! The actual high-score endpoint program returns a rational parameter
within the uniform width. Both the complete parametric recurrence and
the final budget-crossing pass execute on the same bounded ray data.
-/
namespace Blotto.GeneralPaperRayHighSearchSize
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem prepared {m K D E X W P : ℕ} (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hb : Bounded D P beta)
    (lo hi : ℚ) (hl : RationalHeight lo (width D E m X W P)) (hh : RationalHeight hi (width D E m X W P))
    (answer : GeneralPaperRayHighSearch.Answer m K)
    (hr : GeneralPaperRayHighSearch.prepared matrix S h beta x w lo hi=some answer) :
    RationalHeight answer.time (width D E m X W P) := by
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  cases hDP : GeneralPaperRayParametricDP.run query S (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi with
  | none =>
    simp only [GeneralPaperRayHighSearch.prepared,query,hDP] at hr
    contradiction
  | some out =>
    have hFields := GeneralPaperRayAnchorBound.fields D E X W matrix x w hx hw
    have hLen : (GeneralPaperRayAffineScoreInput.fields matrix x w).length≤m := by
      rw [GeneralPaperRayAffineScoreInput.fields_length]
    have hBracket := GeneralPaperRayParametricRunSize.bracket hD hE query _ lo hi hLen hFields hl hh out hDP
    have hTable := GeneralPaperRayAffineDPSize.run D E X W S query _ lo hi hFields out hDP
    rw [GeneralPaperRayAffineScoreInput.fields_length] at hTable
    cases hFinal : GeneralPaperRayFinalBudget.finish matrix out.table x w h beta out.bracket.lower out.bracket.upper with
    | none =>
      simp only [GeneralPaperRayHighSearch.prepared,query,hDP,hFinal] at hr
      contradiction
    | some b =>
      have hSize := GeneralPaperRayParametricRunSize.finish hD hE (Nat.le_refl m) query out.table hTable h beta _ _ hb hBracket.1 hBracket.2 b hFinal
      cases hExtract : GeneralPaperRayHighBlocker.extract m out.table h beta b.lower b.upper with
      | none =>
        simp only [GeneralPaperRayHighSearch.prepared,query,hDP,hFinal,hExtract] at hr
        contradiction
      | some row =>
        have he : (⟨b.lower,row⟩ : GeneralPaperRayHighSearch.Answer m K)=answer := by
          simpa only [GeneralPaperRayHighSearch.prepared,query,hDP,hFinal,hExtract,Option.some.injEq] using hr
        rw [←he]
        exact hSize.1

end Blotto.GeneralPaperRayHighSearchSize
