import Blotto.GeneralPaperEqualNativeSegmentPreparation

/-! Positive labels are selected from an actual stored probability array.
The source reads/tests each probability once. List construction, traversal,
indices, rational comparisons and reference/control work are priced. -/
namespace Blotto.GeneralPaperPositiveLabelScan
set_option autoImplicit false
set_option maxHeartbeats 1200000

def positive (model : RationalCostModel) (A : ℕ) (q : ℚ) : Bool × ℕ :=
  (decide (0 < q), rationalWordWidth q + rationalWordWidth (0 : ℚ) +
    model.rat (max (rationalWordWidth q) (rationalWordWidth (0 : ℚ))) + 32 * A + 32)

def scan {r : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable r ℚ) : List (Fin r) → List (Fin r) × ℕ
  | [] => ([], 32 * A + 32)
  | j :: rest =>
      let current := positive model A (weights.read j)
      let child := scan model A weights rest
      let kept := if current.1 then j :: child.1 else child.1
      (kept, current.2 + child.2 + 64 * (A + binaryWordWidth (j.val + 1) + 1))

theorem data {r : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable r ℚ) (items : List (Fin r)) :
    (scan model A weights items).1 = items.filter (fun j => decide (0 < weights.read j)) := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
    rw [scan, List.filter_cons]
    dsimp only [positive]
    rw [ih]
    simp

def stepBound (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  4 * model.rat (1 + 2 * s) + 128 * (A + binaryWordWidth (r + 1) + 1)

theorem step_work {r s : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable r ℚ)
    (hs : 2 ≤ s) (h : ∀ j, RationalHeight (weights.read j) s) (j : Fin r) :
    (positive model A (weights.read j)).2 + 64 * (A + binaryWordWidth (j.val + 1) + 1) ≤ stepBound model A r s := by
  have hz := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have h1 := (rationalWordWidth_of_height (h j)).trans (model.word_le _)
  have h2 := (rationalWordWidth_of_height hz).trans (model.word_le _)
  have h3 := model.monotone (max_le (rationalWordWidth_of_height (h j)) (rationalWordWidth_of_height hz))
  have hi := binaryWordWidth_mono (show j.val + 1 ≤ r + 1 by omega)
  unfold positive stepBound
  dsimp only
  omega

theorem work {r s : ℕ} (model : RationalCostModel) (A : ℕ) (weights : FixedArrayTable r ℚ)
    (hs : 2 ≤ s) (h : ∀ j, RationalHeight (weights.read j) s) (items : List (Fin r)) :
    (scan model A weights items).2 ≤ items.length * stepBound model A r s + 32 * A + 32 := by
  induction items with
  | nil => simp only [scan, List.length_nil, Nat.zero_mul, Nat.zero_add, le_rfl]
  | cons j rest ih =>
    have hs := step_work model A weights hs h j
    rw [scan]
    dsimp only
    simp only [List.length_cons]
    nlinarith only [ih, hs]

end Blotto.GeneralPaperPositiveLabelScan
