import Blotto.GeneralPaperCircleCDFCount
import Mathlib.Data.Fin.Tuple.Sort

/-! Successful strict and weak thresholds of a sorted row are exactly
initial index segments, including ties, zero bids and empty/full segments. -/
namespace Blotto.GeneralPaperCircleThresholdRank
open GeneralPaperCircleCell
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000

noncomputable def strict {R : ℕ} (x : Fin R → ℝ) (t : ℝ) : ℕ := (Finset.univ.filter (fun i => x i<t)).card
noncomputable def weak {R : ℕ} (x : Fin R → ℝ) (t : ℝ) : ℕ := (Finset.univ.filter (fun i => x i≤t)).card

theorem strict_iff {R : ℕ} (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) (a : Fin R) :
    x a<t ↔ a.val<strict x t := (Tuple.lt_card_lt_iff_apply_lt_of_monotone hx).symm

theorem weak_iff {R : ℕ} (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) (a : Fin R) :
    x a≤t ↔ a.val<weak x t := (Tuple.lt_card_le_iff_apply_le_of_monotone hx).symm

theorem strict_le {R : ℕ} (x : Fin R → ℝ) (t : ℝ) : strict x t≤R :=
  (Finset.card_filter_le _ _).trans_eq (by simp)

theorem weak_le {R : ℕ} (x : Fin R → ℝ) (t : ℝ) : weak x t≤R :=
  (Finset.card_filter_le _ _).trans_eq (by simp)

theorem strict_event (R W : ℕ) (hR : 0<R) (hW : 0<W) (L : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    (Finset.univ.filter (fun c:Fin (R*W) => x (choice R W hR hW c L)<t))=
      GeneralPaperCircleCDFCount.event R W hR hW L (strict x t) := by
  ext c
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,GeneralPaperCircleCDFCount.event]
  exact strict_iff x hx t _

theorem weak_event (R W : ℕ) (hR : 0<R) (hW : 0<W) (L : ℕ) (x : Fin R → ℝ) (hx : Monotone x) (t : ℝ) :
    (Finset.univ.filter (fun c:Fin (R*W) => x (choice R W hR hW c L)≤t))=
      GeneralPaperCircleCDFCount.event R W hR hW L (weak x t) := by
  ext c
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,GeneralPaperCircleCDFCount.event]
  exact weak_iff x hx t _

end Blotto.GeneralPaperCircleThresholdRank
