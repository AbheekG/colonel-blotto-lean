import Blotto.GeneralPaperRayFeasibility

/-! High-tuple feasibility on a forward ray is downward closed from a
feasible start. Combined with the actual static scan, the initial endpoint
query either finishes the ray or gives the feasible/infeasible bracket
needed by the paper's parametric crossing search.
-/
namespace Blotto.GeneralPaperRayBracket
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperStaticRayRows GeneralPaperStaticRayScan GeneralPaperStaticRaySound
open GeneralPaperRayFeasibility GeneralPaperRayAnchorCosts GeneralPaperRayHighSound
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem high_downclosed {m K : ℕ} (scores : Fin m → Fin K → ℕ) (h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) (hStart : HighFeasible scores (costs x w 0) h beta)
    (u : ℚ) (hEnd : HighFeasible scores (costs x w u) h beta) (t : ℚ) (ht : 0≤t ∧ t≤u) :
    HighFeasible scores (costs x w t) h beta := by
  intro labels hl
  have h0 := hStart labels hl
  have hu := hEnd labels hl
  rw [tuple_affine] at h0 hu ⊢
  simp only [zero_mul,add_zero] at h0
  by_cases hw : 0≤∑ j,anchorQ w j (labels j)
  · have hp := mul_nonneg ht.1 hw
    linarith only [h0,hp]
  · have hp := mul_le_mul_of_nonpos_right ht.2 (le_of_not_ge hw)
    linarith only [hu,hp]

theorem test_downclosed {m K : ℕ} (v : RationalFieldSelector m) (hK : 0<K) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) (hStart : test v S h beta x w 0=true)
    (u : ℚ) (hEnd : test v S h beta x w u=true) (t : ℚ) (ht : 0≤t ∧ t≤u) :
    test v S h beta x w t=true := by
  have hi (a : ℚ) := GeneralPaperRayHighSound.passes_iff (score v S) (costs x w a) S h
    (fun l => GeneralPaperComputedThreshold.totalScore_le v S hK l) beta
  exact (hi t).mpr (high_downclosed (score v S) h beta x w ((hi 0).mp hStart) u ((hi u).mp hEnd) t ht)

theorem static_endpoint_or_bracket {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (v : RationalFieldSelector m) (hK : 0<K) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels (score v S) h (beta:ℝ) (fun j => (x j:ℝ)))
    (c : GeneralPaperRayMinimum.Choice (StaticIndex T m K)) (hc : (scan labels x w).choice=some c) :
    (test v S h beta x w c.time=true ∧
      GeneralPaperAffineConstraintRows.Feasible labels (score v S) h (beta:ℝ)
        (fun j => (x j:ℝ)+(c.time:ℝ)*(w j:ℝ)) ∧
      ∀ t : ℚ,c.time<t → ¬GeneralPaperAffineConstraintRows.Feasible labels (score v S) h (beta:ℝ)
        (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))) ∨
    (test v S h beta x w 0=true ∧ test v S h beta x w c.time=false ∧ 0<c.time ∧
      ∀ t : ℚ,0≤t ∧ t≤c.time → StaticFeasible labels (beta:ℝ) x w t) := by
  have hn := GeneralPaperRayMinimumSound.endpoint_nonnegative (evaluate labels x w) (enumerate T m K)
    (fun i _ => initial_residual labels (score v S) h (beta:ℝ) x w hStart i) c hc
  have hStatic := forward_static labels (score v S) h (beta:ℝ) x w hStart c hc
  have hZero : test v S h beta x w 0=true := by
    apply ((full_iff labels v hK S h beta x w 0).mp ?_).2
    simpa only [Rat.cast_zero,zero_mul,add_zero] using hStart
  cases he : test v S h beta x w c.time with
  | true =>
    refine Or.inl ⟨rfl,(full_iff labels v hK S h beta x w c.time).mpr ⟨hStatic c.time ⟨hn,le_rfl⟩,he⟩,?_⟩
    intro t ht hf
    exact beyond_static labels (beta:ℝ) x w c hc t ht ((full_iff labels v hK S h beta x w t).mp hf).1
  | false =>
    refine Or.inr ⟨hZero,rfl,?_,hStatic⟩
    by_contra hp
    have hz : c.time=0 := by linarith only [hn,hp]
    rw [hz,hZero] at he
    contradiction

end Blotto.GeneralPaperRayBracket
