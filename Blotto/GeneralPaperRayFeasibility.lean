import Blotto.GeneralPaperRayAnchorCosts

/-! The actual normalized score selector and rational ray reader join the
executed complete DP query to every original high-tuple constraint, and
then to the full original transfer polytope. No tuple-score-cap premise is
supplied: normalization derives it for the actual score function.
-/
namespace Blotto.GeneralPaperRayFeasibility
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperAffineConstraintSemantics
open GeneralPaperStaticRayRows GeneralPaperStaticRaySound GeneralPaperRayAnchorCosts
open GeneralPaperStrictScore GeneralPaperRayHighMinimum
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

def test {m K : ℕ} (v : RationalFieldSelector m) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) (t : ℚ) : Bool := passes (score v S) (costs x w t) S h beta

theorem high_iff {m K : ℕ} (v : RationalFieldSelector m) (hK : 0<K) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) (t : ℚ) : test v S h beta x w t=true ↔
      ∀ l : HighTuple (score v S) h,(beta:ℝ)≤tupleSum (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ)) l.val := by
  rw [test,GeneralPaperRayHighSound.passes_iff _ _ S h (fun l => GeneralPaperComputedThreshold.totalScore_le v S hK l)]
  constructor
  · intro hf l
    have hh := hf l.val l.property
    have hr : (beta:ℝ)≤((∑ j,costs x w t j (l.val j):ℚ):ℝ) := by exact_mod_cast hh
    rwa [tuple_cast] at hr
  · intro hf l hl
    have hh := hf ⟨l,hl⟩
    rw [←tuple_cast x w t l] at hh
    exact_mod_cast hh

theorem full_iff {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (v : RationalFieldSelector m) (hK : 0<K)
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (t : ℚ) :
    GeneralPaperAffineConstraintRows.Feasible labels (score v S) h (beta:ℝ)
      (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ)) ↔
        StaticFeasible labels (beta:ℝ) x w t ∧ test v S h beta x w t=true := by
  constructor
  · intro hf
    refine ⟨?_,(high_iff v hK S h beta x w t).mpr ?_⟩
    · intro i
      rw [row_eq labels (score v S) h i]
      exact hf (embed i)
    · intro l
      exact (high_tuple_holds labels (score v S) h l (beta:ℝ) _).mp (hf (.inr (.inr (.inr l))))
  · rintro ⟨hs,hh⟩ i
    rcases i with b|o|r|l
    · exact hs (.inl b)
    · exact hs (.inr (.inl o))
    · exact hs (.inr (.inr r))
    · exact (high_tuple_holds labels (score v S) h l (beta:ℝ) _).mpr
        ((high_iff v hK S h beta x w t).mp hh l)

end Blotto.GeneralPaperRayFeasibility
