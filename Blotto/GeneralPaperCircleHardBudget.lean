import Blotto.GeneralPaperCircleArcPartition

/-! Every finite-cell reconstruction preserves the complete row's hard
at-most budget. Representative coordinates may be arbitrarily correlated;
the proof is pointwise in the row and the common shift. -/
namespace Blotto.GeneralPaperCircleHardBudget
open GeneralPaperCircleCell GeneralPaperCircleArcPartition
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def lengths {g : ℕ} (R : ℕ) (weights : Fin g → ℕ) : Fin g → ℕ := fun j => R*weights j

noncomputable def bid {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (weights : Fin g → ℕ) (x : Fin R → ℝ) (shift : ℕ) : Allocation g := fun j =>
  ((lengths R weights j:ℝ)/W)*x (choice R W hR hW
    (cell (R*W) (Nat.mul_pos hR hW) shift (before (lengths R weights) j.val)) (lengths R weights j))

theorem lengths_total {g : ℕ} (R W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) :
    (∑ j,lengths R weights j)=R*W := by
  unfold lengths
  rw [←Finset.mul_sum,hs]

theorem sum_bound {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (x : Fin R → ℝ) (hx : Monotone x) (shift : ℕ) :
    (∑ j,bid R W hR hW weights x shift j)≤∑ a,x a := by
  have h := arc_total (lengths R weights) R W hR hW (lengths_total R W weights hs) shift x hx
  unfold bid
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div]
  apply (div_le_iff₀ (by exact_mod_cast hW : (0:ℝ)<W)).mpr
  nlinarith only [h]

theorem nonnegative {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (x : Fin R → ℝ) (hx : ∀ a,0≤x a) (shift : ℕ) (j : Fin g) :
    0≤bid R W hR hW weights x shift j := by
  unfold bid
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hx _)

theorem feasible {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (x : Fin R → ℝ) (hx : Monotone x) (h0 : ∀ a,0≤x a)
    (B : ℝ) (hB : ∑ a,x a≤B) (shift : ℕ) : Feasible B (bid R W hR hW weights x shift) :=
  ⟨nonnegative R W hR hW weights x h0 shift,(sum_bound R W hR hW weights hs x hx shift).trans hB⟩

noncomputable def reconstruct {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (weights : Fin g → ℕ) (kept : Allocation h) (x : Fin R → ℝ) (shift : ℕ) : Allocation (h+g) :=
  Fin.addCases kept (bid R W hR hW weights x shift)

theorem reconstruct_kept {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (kept : Allocation h) (x : Fin R → ℝ) (shift : ℕ) (i : Fin h) :
    reconstruct R W hR hW weights kept x shift (Fin.castAdd g i)=kept i := by
  simp only [reconstruct,Fin.addCases_left]

theorem reconstruct_light {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (kept : Allocation h) (x : Fin R → ℝ) (shift : ℕ) (j : Fin g) :
    reconstruct R W hR hW weights kept x shift (Fin.natAdd h j)=bid R W hR hW weights x shift j := by
  simp only [reconstruct,Fin.addCases_right]

theorem reconstruct_feasible {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (kept : Allocation h) (x : Fin R → ℝ) (hx : Monotone x)
    (B : ℝ) (hRow : Feasible B (Fin.addCases kept x)) (shift : ℕ) :
    Feasible B (reconstruct R W hR hW weights kept x shift) := by
  have hk : ∀ i,0≤kept i := fun i => by simpa only [Fin.addCases_left] using hRow.1 (Fin.castAdd R i)
  have h0 : ∀ a,0≤x a := fun a => by simpa only [Fin.addCases_right] using hRow.1 (Fin.natAdd h a)
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [reconstruct_kept] using hk i
    · intro a
      simpa only [reconstruct_light] using nonnegative R W hR hW weights x h0 shift a
  · rw [Fin.sum_univ_add]
    simp only [reconstruct_kept,reconstruct_light]
    have hb := hRow.2
    rw [Fin.sum_univ_add] at hb
    simp only [Fin.addCases_left,Fin.addCases_right] at hb
    have hh := sum_bound R W hR hW weights hs x hx shift
    linarith only [hb,hh]

end Blotto.GeneralPaperCircleHardBudget
