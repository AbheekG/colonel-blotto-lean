import Blotto.GeneralPaperCircleSortedComparison

/-! The actual uniform lower-quantile comparator of a finite uniform law.
For a sorted W-point row Y, q_0=0 and q_a=Y_{ceil(aW/R)-1} for a>0.
Its explicit index is (aW-1)/R. These are erased comparison deviations,
not a runtime enumeration or a nonuniform quantile-floor pushforward. -/
namespace Blotto.GeneralPaperLowerQuantile
open GeneralPaperCircleThresholdRank
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def index (R W : ℕ) (hR : 0<R) (hW : 0<W) (a : Fin R) : Fin W :=
  ⟨(a.val*W-1)/R,(Nat.div_lt_iff_lt_mul hR).mpr (by
    have h := Nat.mul_lt_mul_of_pos_right a.isLt hW
    rw [Nat.mul_comm W R]
    omega)⟩

noncomputable def row (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (a : Fin R) : ℝ :=
  if a.val=0 then 0 else Y (index R W hR hW a)

theorem index_rank (R W : ℕ) (hR : 0<R) (hW : 0<W) (a : Fin R) (ha : a.val≠0) (f : ℕ) :
    (index R W hR hW a).val<f ↔ a.val*W≤R*f := by
  change (a.val*W-1)/R<f ↔ _
  rw [Nat.div_lt_iff_lt_mul hR,Nat.mul_comm f R]
  have hp := Nat.mul_pos (Nat.pos_of_ne_zero ha) hW
  omega

theorem zero (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) : row R W hR hW Y ⟨0,hR⟩=0 := by
  simp only [row,ite_true]

theorem nonnegative (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : ∀ i,0≤Y i) (a : Fin R) :
    0≤row R W hR hW Y a := by
  unfold row
  split_ifs
  · exact le_rfl
  · exact hY _

theorem weak_test (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y)
    (t : ℝ) (ht : 0≤t) (a : Fin R) :
    row R W hR hW Y a≤t ↔ a.val*W≤R*weak Y t := by
  by_cases ha : a.val=0
  · rw [row,ite_eq_left ha,ha]
    simp only [Nat.zero_mul,Nat.zero_le,ht]
  · rw [row,ite_eq_right ha,weak_iff Y hY t,index_rank R W hR hW a ha]

theorem strict_test (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y)
    (t : ℝ) (ht : 0<t) (a : Fin R) :
    row R W hR hW Y a<t ↔ a.val*W≤R*strict Y t := by
  by_cases ha : a.val=0
  · rw [row,ite_eq_left ha,ha]
    simp only [Nat.zero_mul,Nat.zero_le,ht]
  · rw [row,ite_eq_right ha,strict_iff Y hY t,index_rank R W hR hW a ha]

end Blotto.GeneralPaperLowerQuantile
