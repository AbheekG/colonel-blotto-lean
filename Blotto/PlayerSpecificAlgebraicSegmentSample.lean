import Blotto.PlayerSpecificAlgebraicSegment

/-! Bounded finite segment selection. Each reached slot uses one fresh
H-bit block with its conditional algebraic weight; a final fallback slot
needs no coin. A fresh K-bit midpoint interpolates the chosen segment. -/
namespace Blotto.PlayerSpecificAlgebraicSegmentSample
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def select {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) : List (Fin slots) → Data → List (Fin H → Bool) → Fin slots × ℕ
  | [],_,_ => (fallback,0)
  | slot::rest,remaining,blocks =>
      let probability:=PlayerSpecificAlgebraicField.divide root.polynomial (weights.read slot) remaining
      if PlayerSpecificAlgebraicMidpointCoin.run model root probability H (blocks.headD (fun _ => false)) then
        (slot,1)
      else
        let next:=PlayerSpecificAlgebraicField.minus root.polynomial remaining (weights.read slot)
        let result:=select model root weights fallback H rest next blocks.tail
        (result.1,result.2+1)

theorem select_visits {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (items : List (Fin slots)) (remaining : Data) (blocks : List (Fin H → Bool)) :
    (select model root weights fallback H items remaining blocks).2≤ items.length := by
  induction items generalizing remaining blocks with
  | nil => exact Nat.le_refl 0
  | cons slot rest ih =>
      simp only [select]
      split
      · simp only [List.length_cons]; omega
      · exact Nat.add_le_add_right (ih _ _) 1

def selected {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H : ℕ) (bits : Fin ((slots-1)*H) → Bool) : Fin slots × ℕ :=
  select model root d.weights fallback H ((List.finRange slots).take (slots-1))
    (PlayerSpecificAlgebraicField.constant root.polynomial 1) (PlayerSpecificFiniteResourceLoop.blocks (slots-1) H bits)

theorem selected_visits {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H : ℕ) (bits : Fin ((slots-1)*H) → Bool) :
    (selected model root d fallback H bits).2≤slots-1 :=
  (select_visits model root d.weights fallback H _ _ _).trans (List.length_take_le _ _)

def sample {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H K : ℕ) (bits : Fin ((slots-1)*H+K) → Bool) : FixedArrayTable N Data :=
  let choice:=selected model root d fallback H (firstBitBlock ((slots-1)*H) K bits)
  let midpoint:=dyadicMidpointSample K (secondBitBlock ((slots-1)*H) K bits)
  interpolate root d choice.1 midpoint

theorem budget {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H K : ℕ) (bits : Fin ((slots-1)*H+K) → Bool) (x B : ℝ)
    (hx : realEvaluate root.polynomial x=0)
    (hP : ∀ slot,FullBudget B (values (d.first.read slot) x))
    (hQ : ∀ slot,FullBudget B (values (d.second.read slot) x)) :
    FullBudget B (values (sample model root d fallback H K bits) x) := by
  apply interpolate_budget root d _ _ x B hx
  · have h:=dyadicMidpointSample_bounds K (secondBitBlock ((slots-1)*H) K bits)
    exact_mod_cast (And.intro h.1.le h.2.le)
  · exact hP _
  · exact hQ _

theorem box {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H K : ℕ) (bits : Fin ((slots-1)*H+K) → Bool) (x : ℝ) (length : Allocation N)
    (hx : realEvaluate root.polynomial x=0)
    (hP : ∀ slot,InBox length (values (d.first.read slot) x))
    (hQ : ∀ slot,InBox length (values (d.second.read slot) x)) :
    InBox length (values (sample model root d fallback H K bits) x) := by
  apply interpolate_box root d _ _ x length hx
  · have h:=dyadicMidpointSample_bounds K (secondBitBlock ((slots-1)*H) K bits)
    exact_mod_cast (And.intro h.1.le h.2.le)
  · exact hP _
  · exact hQ _

end Blotto.PlayerSpecificAlgebraicSegmentSample
