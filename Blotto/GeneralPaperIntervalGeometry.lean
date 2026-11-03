import Blotto.GeneralPaperIntervalCache

/-! At most two query boundaries can force a contiguous interval update to
descend. This integer-valued potential avoids an exponential full-tree visit
bound: child boundary counts sum to at most the parent's count.
-/
namespace Blotto.GeneralPaperIntervalGeometry
set_option autoImplicit false

def inside (start span point : ℚ) : ℕ := if start<point ∧ point<start+span then 1 else 0

def boundaries (start span lo hi : ℚ) : ℕ := inside start span lo+inside start span hi

def Disjoint (start span lo hi : ℚ) : Prop := hi≤start ∨ start+span≤lo

def Covered (start span lo hi : ℚ) : Prop := lo≤start ∧ start+span≤hi

instance (start span lo hi : ℚ) : Decidable (Disjoint start span lo hi) := inferInstanceAs (Decidable (_ ∨ _))
instance (start span lo hi : ℚ) : Decidable (Covered start span lo hi) := inferInstanceAs (Decidable (_ ∧ _))

theorem inside_le_one (start span point : ℚ) : inside start span point≤1 := by unfold inside; split <;> omega

theorem boundaries_le_two (start span lo hi : ℚ) : boundaries start span lo hi≤2 := by
  have hl := inside_le_one start span lo
  have hh := inside_le_one start span hi
  unfold boundaries
  omega

theorem child_inside (start span point : ℚ) (hSpan : 0<span) :
    inside start (span/2) point+inside (start+span/2) (span/2) point≤ inside start span point := by
  have hLeft : (start<point ∧ point<start+span/2) → start<point ∧ point<start+span := by
    intro h
    exact ⟨h.1,by linarith [h.2]⟩
  have hRight : (start+span/2<point ∧ point<start+span/2+span/2) → start<point ∧ point<start+span := by
    intro h
    constructor <;> linarith [h.1,h.2]
  unfold inside
  by_cases hl : start<point ∧ point<start+span/2
  · have hr : ¬(start+span/2<point ∧ point<start+span/2+span/2) := by intro h; linarith [hl.2,h.1]
    simp only [if_pos hl,if_neg hr,if_pos (hLeft hl)]
    omega
  · by_cases hr : start+span/2<point ∧ point<start+span/2+span/2
    · simp only [if_neg hl,if_pos hr,if_pos (hRight hr)]
      omega
    · simp only [if_neg hl,if_neg hr]
      exact Nat.zero_le _

theorem child_boundaries (start span lo hi : ℚ) (hSpan : 0<span) :
    boundaries start (span/2) lo hi+boundaries (start+span/2) (span/2) lo hi≤boundaries start span lo hi := by
  have hl := child_inside start span lo hSpan
  have hh := child_inside start span hi hSpan
  unfold boundaries
  omega

theorem partial_has_boundary (start span lo hi : ℚ)
    (hDisjoint : ¬Disjoint start span lo hi) (hCovered : ¬Covered start span lo hi) :
    1≤boundaries start span lo hi := by
  have h1 : lo<start+span := by unfold Disjoint at hDisjoint; push_neg at hDisjoint; exact hDisjoint.2
  have h2 : start<hi := by unfold Disjoint at hDisjoint; push_neg at hDisjoint; exact hDisjoint.1
  by_cases hl : start<lo
  · have hInside : inside start span lo=1 := by unfold inside; rw [if_pos ⟨hl,h1⟩]
    unfold boundaries
    rw [hInside]
    omega
  · have hr : hi<start+span := by
      unfold Covered at hCovered
      by_contra hh
      exact hCovered ⟨by linarith,by linarith⟩
    have hInside : inside start span hi=1 := by unfold inside; rw [if_pos ⟨h2,hr⟩]
    unfold boundaries
    rw [hInside]
    omega

end Blotto.GeneralPaperIntervalGeometry
