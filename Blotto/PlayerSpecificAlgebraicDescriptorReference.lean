import Blotto.PlayerSpecificAlgebraicNestedParameterSizes

/-! Exact real-lottery interpretation of actual cached algebraic rows.
This proof-only relation transfers endpoint guarantees to executing draws. -/
namespace Blotto.PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

structure Refines {N slots : ℕ} (d : Descriptor N slots) (x : ℝ) (l : SegmentLottery N slots) : Prop where
  weights : ∀ slot,realEvaluate (d.weights.read slot) x=l.weight slot
  first : ∀ slot,values (d.first.read slot) x=l.P slot
  second : ∀ slot,values (d.second.read slot) x=l.Q slot

theorem sample_budget {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H K : ℕ) (bits : Fin ((slots-1)*H+K) → Bool) (x B : ℝ)
    (l : SegmentLottery N slots) (hr : Refines d x l) (hx : realEvaluate root.polynomial x=0)
    (hP : ∀ slot,FullBudget B (l.P slot)) (hQ : ∀ slot,FullBudget B (l.Q slot)) :
    FullBudget B (values (PlayerSpecificAlgebraicSegmentSample.sample model root d fallback H K bits) x) := by
  apply PlayerSpecificAlgebraicSegmentSample.budget model root d fallback H K bits x B hx
  · intro slot; rw [hr.first slot]; exact hP slot
  · intro slot; rw [hr.second slot]; exact hQ slot

theorem sample_box {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H K : ℕ) (bits : Fin ((slots-1)*H+K) → Bool) (x : ℝ) (length : Allocation N)
    (l : SegmentLottery N slots) (hr : Refines d x l) (hx : realEvaluate root.polynomial x=0)
    (hP : ∀ slot,InBox length (l.P slot)) (hQ : ∀ slot,InBox length (l.Q slot)) :
    InBox length (values (PlayerSpecificAlgebraicSegmentSample.sample model root d fallback H K bits) x) := by
  apply PlayerSpecificAlgebraicSegmentSample.box model root d fallback H K bits x length hx
  · intro slot; rw [hr.first slot]; exact hP slot
  · intro slot; rw [hr.second slot]; exact hQ slot

end Blotto.PlayerSpecificAlgebraicDescriptorReference
