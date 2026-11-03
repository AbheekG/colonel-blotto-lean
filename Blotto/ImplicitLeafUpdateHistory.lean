import Blotto.ImplicitLeafUpdate
import Blotto.ImplicitLeafGuideSize

/-! Actual sparse block histories refine stored rounded field histories.
Only one selected field is changed per observation and each change adds at
most two blocks. Rational bid decoding must still supply the two exact cut
regions; no numerical universe is traversed by this history constructor. -/

namespace Blotto
open scoped Classical
namespace ImplicitLeafCounts

def blockHistory {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m)
    (weak strict : List (Fin a) → Fin a → ℤ) (eta theta : ℚ) : List (Fin a) → Fin m → List Block
  | [] => fun field => [⟨0, caps field, 1⟩]
  | x :: past =>
    let old := blockHistory caps selected weak strict eta theta past
    Function.update old (selected past x)
      (updateBlocks (weak past x) (strict past x) eta theta (old (selected past x)))

def cutLoss {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m)
    (weak strict : List (Fin a) → Fin a → ℤ)
    (past : List (Fin a)) (x : Fin a) (code : Fin (caps (selected past x) + 1)) : ℚ :=
  regionLoss (weak past x) (strict past x) code.val

theorem cutLoss_unit {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m) (weak strict : List (Fin a) → Fin a → ℤ) :
    ∀ past x code, 0 ≤ cutLoss caps selected weak strict past x code ∧ cutLoss caps selected weak strict past x code ≤ 1 :=
  fun _ _ _ => regionLoss_unit _ _ _

theorem blockHistory_partition {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m) (weak strict : List (Fin a) → Fin a → ℤ)
    (eta theta : ℚ) (past : List (Fin a)) : ∀ field,
    Partition (caps field) (blockHistory caps selected weak strict eta theta past field) := by
  induction past with
  | nil => intro field; simp [blockHistory, Partition, CoversFrom]
  | cons x past ih =>
    intro field
    by_cases he : field = selected past x
    · subst field
      simp only [blockHistory, Function.update_self]
      exact updateBlocks_partition _ _ (ih _) _ _ _ _
    · simp only [blockHistory, Function.update_of_ne he]
      exact ih field

theorem blockHistory_positive {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m) (weak strict : List (Fin a) → Fin a → ℤ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) : ∀ field, Positive (blockHistory caps selected weak strict eta theta past field) := by
  induction past with
  | nil => intro field atom ha; simpa only [blockHistory, List.mem_singleton] using
      (show atom ∈ [⟨0, caps field, 1⟩] → 0 < atom.weight from fun he => by
        have ha : atom = (⟨0, caps field, 1⟩ : Block) := by simpa only [List.mem_singleton] using he
        simp [ha]) ha
  | cons x past ih =>
    intro field
    by_cases he : field = selected past x
    · subst field
      simp only [blockHistory, Function.update_self]
      exact updateBlocks_positive _ (ih _) _ _ eta theta heta htheta
    · simp only [blockHistory, Function.update_of_ne he]
      exact ih field

theorem blockHistory_refines {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m) (weak strict : List (Fin a) → Fin a → ℤ)
    (eta theta : ℚ) (past : List (Fin a)) : ∀ field (code : Fin (caps field + 1)),
    labelMass (blockHistory caps selected weak strict eta theta past field) code.val =
      SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected (cutLoss caps selected weak strict) eta theta past field code := by
  induction past with
  | nil =>
    intro field code
    have hi : contains (⟨0, caps field, 1⟩ : Block) code.val = true := by
      simp only [contains, decide_eq_true_eq]
      omega
    simp only [blockHistory, labelMass, hi, ite_true, add_zero, SparseMW.roundedFieldHistory]
  | cons x past ih =>
    intro field code
    by_cases he : field = selected past x
    · subst field
      simp only [blockHistory, SparseMW.roundedFieldHistory, Function.update_self]
      rw [updateBlocks_labelMass _ _ (blockHistory_partition caps selected weak strict eta theta past _) _ _ _ _ code, ih]
      rfl
    · simp only [blockHistory, SparseMW.roundedFieldHistory, Function.update_of_ne he]
      exact ih field code

theorem blockHistory_length {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m) (weak strict : List (Fin a) → Fin a → ℤ)
    (eta theta : ℚ) (past : List (Fin a)) : ∀ field,
    (blockHistory caps selected weak strict eta theta past field).length ≤
      1 + 2 * SparseMW.fieldUpdateCount selected past field := by
  induction past with
  | nil => intro field; simp [blockHistory, SparseMW.fieldUpdateCount]
  | cons x past ih =>
    intro field
    by_cases he : field = selected past x
    · subst field
      simp only [blockHistory, Function.update_self, SparseMW.fieldUpdateCount, ite_true]
      have hu := updateBlocks_length (blockHistory caps selected weak strict eta theta past (selected past x))
        (weak past x) (strict past x) eta theta
      have hi := ih (selected past x)
      omega
    · simp only [blockHistory, Function.update_of_ne he, SparseMW.fieldUpdateCount, he, ite_false, Nat.add_zero]
      exact ih field

theorem blockHistory_refines_loss {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m) (weak strict : List (Fin a) → Fin a → ℤ)
    (localLoss : (past : List (Fin a)) → (x : Fin a) → Fin (caps (selected past x) + 1) → ℚ)
    (hLoss : ∀ past x code, localLoss past x code = cutLoss caps selected weak strict past x code)
    (eta theta : ℚ) (past : List (Fin a)) : ∀ field (code : Fin (caps field + 1)),
    labelMass (blockHistory caps selected weak strict eta theta past field) code.val =
      SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected localLoss eta theta past field code := by
  have he : localLoss = cutLoss caps selected weak strict := by funext past x code; exact hLoss past x code
  rw [he]
  exact blockHistory_refines caps selected weak strict eta theta past

theorem blockHistory_leafGuide_length {a m : ℕ} (caps : Fin m → ℕ)
    (selected : List (Fin a) → Fin a → Fin m) (weak strict : List (Fin a) → Fin a → ℤ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m)
    (resource : Fin (caps field + 1) → ℚ) (hr : ∀ code, 0 ≤ resource code)
    (hzero : resource ⟨0, by omega⟩ = 0) (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((CumulativeGuideSorting.guideAtoms
      (leafAtoms (caps field) (blockHistory caps selected weak strict eta theta past field) resource) (1 + delta)).length : ℝ) ≤
      1 + 2 * (Real.log ((caps field + 1 : ℕ) : ℝ) +
        (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) / (delta : ℝ) := by
  apply rounded_leafGuide_length_bound (sizes := fun field => caps field + 1) selected (cutLoss caps selected weak strict) eta theta heta htheta
    (cutLoss_unit caps selected weak strict) past field (caps field) rfl
    (blockHistory caps selected weak strict eta theta past field)
    (blockHistory_partition caps selected weak strict eta theta past field)
    (blockHistory_positive caps selected weak strict eta theta heta htheta past field)
    (blockHistory_refines caps selected weak strict eta theta past field) resource hr hzero delta hd hu

end ImplicitLeafCounts
end Blotto
