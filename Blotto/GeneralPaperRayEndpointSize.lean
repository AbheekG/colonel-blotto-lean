import Blotto.GeneralPaperRayHighSearchSize

/-! The complete native static-or-high endpoint program has a uniform
returned-parameter height. The actual original-basis stage supplies all
ray data and size premises and returns the same original blocker/update
contract. No endpoint or affine-size oracle is supplied.
-/
namespace Blotto.GeneralPaperRayEndpointSize
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperRayUniformSize
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperProxyParameters
open GeneralPaperBasisOriginalDirection
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem prepared {T m K D E X W P : ℕ} (hm : 0<m) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hb : Bounded D P beta)
    (answer : GeneralPaperRayEndpoint.Answer T m K)
    (hr : GeneralPaperRayEndpoint.prepared labels matrix S h beta x w=some answer) :
    RationalHeight answer.time (width D E m X W P) := by
  cases hs : (GeneralPaperStaticRayScan.scan labels x w).choice with
  | none =>
    simp only [GeneralPaperRayEndpoint.prepared,hs] at hr
    contradiction
  | some c =>
    have hStatic := static_time hm hD hE labels (GeneralPaperRayQueryWork.scores matrix) h beta x w hx hw hb c hs
    by_cases ht : (GeneralPaperRayPricedPredicate.query matrix x w S h beta c.time).1=true
    · have he : (⟨c.time,.inl c.blocker⟩ : GeneralPaperRayEndpoint.Answer T m K)=answer := by
        simpa only [GeneralPaperRayEndpoint.prepared,hs,ht,ite_true,Option.some.injEq] using hr
      rw [←he]
      exact hStatic
    · cases hHigh : GeneralPaperRayHighSearch.prepared matrix S h beta x w 0 c.time with
      | none =>
        simp only [GeneralPaperRayEndpoint.prepared,hs,ht,Bool.false_eq_true,ite_false,hHigh,Option.map_none] at hr
        contradiction
      | some high =>
        have hPositive : 0<width D E m X W P := by
          have hw := binaryWordWidth_pos D
          unfold width GeneralPaperRayAffineBound.rootWidth
          omega
        have hZero := GeneralPaperQuantizedHeight.zero_height _ hPositive
        have hSize := GeneralPaperRayHighSearchSize.prepared hD hE matrix S h beta x w hx hw hb 0 c.time hZero hStatic high hHigh
        have he : (⟨high.time,.inr high.labels⟩ : GeneralPaperRayEndpoint.Answer T m K)=answer := by
          simpa only [GeneralPaperRayEndpoint.prepared,hs,ht,Bool.false_eq_true,ite_false,hHigh,Option.map_some,Option.some.injEq] using hr
        rw [←he]
        exact hSize

theorem stage_return {T m j : ℕ} (k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (hK : 0<(prepare m k).K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*((prepare m k).K-1))) (state : State j (m*((prepare m k).K-1)))
    (hj : j<m*((prepare m k).K-1)) (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state) :
    ∃ answer,GeneralPaperRayEndpoint.prepared dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h
      ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)=some answer ∧
      RationalHeight answer.time
        (width (N*state.determinant.natAbs) state.determinant.natAbs m 1 (j*(prepare m k).H*(m+1)+1) betaN.natAbs) ∧
      GeneralPaperBasisAdvanceSize.Contract k dict.label state hj answer := by
  obtain ⟨answer,hr,hUpdate⟩ := GeneralPaperBasisAdvanceSize.actual_ray k hm scoreDepth dict v hK S h N hCap betaN initialGrid state hj inv
  have hx := GeneralPaperRayAnchorBound.point k dict v S h N hN betaN initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hb := GeneralPaperRayAnchorBound.budget N hN state.determinant.natAbs betaN
  exact ⟨answer,hr,prepared hm (Nat.mul_pos hN (Int.natAbs_pos.mpr inv.nonzero)) (Int.natAbs_pos.mpr inv.nonzero)
    _ _ S h _ _ _ hx hw hb answer hr,hUpdate⟩

end Blotto.GeneralPaperRayEndpointSize
