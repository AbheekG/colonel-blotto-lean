import Blotto.ImplicitGibbsPreparedSampler

/-! Succinct rounded block histories accept observations of an arbitrary
type. They never encode or enumerate observations or local code universes.
Computed monotone resource cuts determine each native single-field update. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

def genericBlocks {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) : List α → Fin m → List Block
  | [] => fun field => [⟨0, caps field, 1⟩]
  | x :: past =>
    let old := genericBlocks caps decode selected opponent eta theta past
    let field := selected past x
    Function.update old field (updateBlocks
      (MonotoneResourceCuts.weak (caps field) (decode field) (opponent past x)).1
      (MonotoneResourceCuts.strict (caps field) (decode field) (opponent past x)).1 eta theta (old field))

def genericLoss {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ)
    (past : List α) (x : α) (code : Fin (caps (selected past x) + 1)) : ℚ :=
  SparseMW.rationalShare (opponent past x) (decode (selected past x) code.val)

def genericFields {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) :
    List α → (field : Fin m) → Fin (caps field + 1) → ℚ
  | [] => fun _ _ => 1
  | x :: past =>
    let old := genericFields caps decode selected opponent eta theta past
    Function.update old (selected past x) (fun code => SparseMW.storedUpdate (old (selected past x) code) eta
      (genericLoss caps decode selected opponent past x code) theta)

def genericCount {α : Type*} {m : ℕ} (selected : List α → α → Fin m) : List α → Fin m → ℕ
  | [] => fun _ => 0
  | x :: past => fun field => genericCount selected past field + if field = selected past x then 1 else 0

theorem genericCount_sum {α : Type*} {m : ℕ} (selected : List α → α → Fin m) (past : List α) :
    (∑ field, genericCount selected past field) = past.length := by
  induction past with
  | nil => simp [genericCount]
  | cons x past ih => simp [genericCount, Finset.sum_add_distrib, ih]

theorem genericCount_le_length {α : Type*} {m : ℕ} (selected : List α → α → Fin m) (past : List α) (field : Fin m) :
    genericCount selected past field ≤ past.length := by
  induction past with
  | nil => exact le_rfl
  | cons x past ih => simp only [genericCount, List.length_cons]; split_ifs <;> omega

theorem genericLoss_unit {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) :
    ∀ past x code, 0 ≤ genericLoss caps decode selected opponent past x code ∧ genericLoss caps decode selected opponent past x code ≤ 1 :=
  fun _ _ _ => SparseMW.rationalShare_unit _ _

theorem genericBlocks_partition {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) (past : List α) :
    ∀ field, Partition (caps field) (genericBlocks caps decode selected opponent eta theta past field) := by
  induction past with
  | nil => intro field; simp [genericBlocks, Partition, CoversFrom]
  | cons x past ih =>
    intro field
    by_cases he : field = selected past x
    · subst field
      simp only [genericBlocks, Function.update_self]
      exact updateBlocks_partition _ _ (ih _) _ _ _ _
    · simp only [genericBlocks, Function.update_of_ne he]
      exact ih field

theorem genericBlocks_positive {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) :
    ∀ field, Positive (genericBlocks caps decode selected opponent eta theta past field) := by
  induction past with
  | nil =>
    intro field block hb
    have he : block = (⟨0, caps field, 1⟩ : Block) := by simpa [genericBlocks] using hb
    simp [he]
  | cons x past ih =>
    intro field
    by_cases he : field = selected past x
    · subst field
      simp only [genericBlocks, Function.update_self]
      exact updateBlocks_positive _ (ih _) _ _ eta theta heta htheta
    · simp only [genericBlocks, Function.update_of_ne he]
      exact ih field

theorem genericBlocks_refines {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) (past : List α) :
    ∀ field (code : Fin (caps field + 1)), labelMass (genericBlocks caps decode selected opponent eta theta past field) code.val =
      genericFields caps decode selected opponent eta theta past field code := by
  induction past with
  | nil => intro field code; simp [genericBlocks, genericFields, labelMass, contains, show code.val ≤ caps field by omega]
  | cons x past ih =>
    intro field code
    by_cases he : field = selected past x
    · subst field
      simp only [genericBlocks, genericFields, Function.update_self]
      rw [updateBlocks_labelMass _ _ (genericBlocks_partition caps decode selected opponent eta theta past _) _ _ _ _ code, ih]
      rw [MonotoneResourceCuts.regionLoss_exact _ _ (hm _) _ code.val (by omega)]
      rfl
    · simp only [genericBlocks, genericFields, Function.update_of_ne he]
      exact ih field code

theorem genericBlocks_length {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) (past : List α) :
    ∀ field, (genericBlocks caps decode selected opponent eta theta past field).length ≤ 1 + 2 * genericCount selected past field := by
  induction past with
  | nil => intro field; simp [genericBlocks, genericCount]
  | cons x past ih =>
    intro field
    by_cases he : field = selected past x
    · subst field
      simp only [genericBlocks, Function.update_self, genericCount, ite_true]
      have hu := updateBlocks_length (genericBlocks caps decode selected opponent eta theta past (selected past x))
        ((MonotoneResourceCuts.weak (caps (selected past x)) (decode (selected past x)) (opponent past x)).1 : ℤ)
        ((MonotoneResourceCuts.strict (caps (selected past x)) (decode (selected past x)) (opponent past x)).1 : ℤ) eta theta
      have hi := ih (selected past x)
      omega
    · simp only [genericBlocks, Function.update_of_ne he, genericCount, he, ite_false, Nat.add_zero]
      exact ih field

theorem genericFields_positive {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) :
    ∀ field code, 0 < genericFields caps decode selected opponent eta theta past field code := by
  intro field code
  rw [← genericBlocks_refines caps decode hm selected opponent eta theta past field code]
  exact partition_labelMass_positive _ _ (genericBlocks_partition caps decode selected opponent eta theta past field)
    (genericBlocks_positive caps decode selected opponent eta theta heta htheta past field) code

theorem genericFields_le_one {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) :
    ∀ field code, genericFields caps decode selected opponent eta theta past field code ≤ 1 := by
  induction past with
  | nil => intro field code; exact le_rfl
  | cons x past ih =>
    intro field code
    by_cases he : field = selected past x
    · subst field
      simp only [genericFields, Function.update_self]
      have hl := genericLoss_unit caps decode selected opponent past x code
      exact (SparseMW.storedUpdate_decreases _ _ _ _ (genericFields_positive caps decode hm selected opponent eta theta heta htheta past _ _)
        ⟨mul_nonneg heta.1.le hl.1, (mul_le_of_le_one_right heta.1.le hl.2).trans heta.2⟩ htheta).trans (ih _ _)
    · simp only [genericFields, Function.update_of_ne he]
      exact ih field code

theorem genericFields_exp_lower {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) :
    ∀ field code, Real.exp (-(genericCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) ≤
      (genericFields caps decode selected opponent eta theta past field code : ℝ) := by
  induction past with
  | nil => intro field code; simp [genericCount, genericFields]
  | cons x past ih =>
    intro field code
    by_cases he : field = selected past x
    · subst field
      have hOld := genericFields_positive caps decode hm selected opponent eta theta heta htheta past _ code
      have hl := genericLoss_unit caps decode selected opponent past x code
      have hx : 0 ≤ eta * genericLoss caps decode selected opponent past x code ∧ eta * genericLoss caps decode selected opponent past x code ≤ 1 / 4 :=
        ⟨mul_nonneg heta.1.le hl.1, (mul_le_of_le_one_right heta.1.le hl.2).trans heta.2⟩
      have hCert := (SparseMW.storedRatio_certificate _ eta (genericLoss caps decode selected opponent past x code) theta hOld hx htheta).1
      have hLoss : (eta : ℝ) * (genericLoss caps decode selected opponent past x code : ℝ) ≤ (eta : ℝ) := by
        exact_mod_cast mul_le_of_le_one_right heta.1.le hl.2
      have hDecay : Real.exp (-((eta : ℝ) + 3 * (theta : ℝ))) ≤
          (SparseMW.storedRatio (genericFields caps decode selected opponent eta theta past (selected past x) code) eta
            (genericLoss caps decode selected opponent past x code) theta : ℝ) := (Real.exp_le_exp.mpr (by linarith)).trans hCert
      have hProduct := mul_le_mul (ih _ code) hDecay (Real.exp_pos _).le (by exact_mod_cast hOld.le)
      have hExact := SparseMW.storedUpdate_exact_ratio _ eta (genericLoss caps decode selected opponent past x code) theta (ne_of_gt hOld)
      have hExactR : (genericFields caps decode selected opponent eta theta past (selected past x) code : ℝ) *
          (SparseMW.storedRatio (genericFields caps decode selected opponent eta theta past (selected past x) code) eta
            (genericLoss caps decode selected opponent past x code) theta : ℝ) =
          (SparseMW.storedUpdate (genericFields caps decode selected opponent eta theta past (selected past x) code) eta
            (genericLoss caps decode selected opponent past x code) theta : ℝ) := by exact_mod_cast hExact
      rw [hExactR, ← Real.exp_add] at hProduct
      simp only [genericCount, ite_true, Nat.cast_add, Nat.cast_one, genericFields, Function.update_self]
      convert hProduct using 1
      congr 1
      ring
    · simp only [genericCount, he, ite_false, Nat.add_zero, genericFields, Function.update_of_ne he]
      exact ih field code

theorem genericBlocks_log_range {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (field : Fin m) :
    Real.log ((totalMass (genericBlocks caps decode selected opponent eta theta past field) : ℝ) /
      (prefixMass (genericBlocks caps decode selected opponent eta theta past field) 0 : ℝ)) ≤
      Real.log ((caps field + 1 : ℕ) : ℝ) + (genericCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ)) := by
  let blocks := genericBlocks caps decode selected opponent eta theta past field
  have hp := genericBlocks_partition caps decode selected opponent eta theta past field
  have hw := genericBlocks_positive caps decode selected opponent eta theta heta htheta past field
  apply partition_log_range (caps field) blocks hp hw
  · rw [partition_prefix_zero _ _ hp, genericBlocks_refines caps decode hm selected opponent eta theta past field ⟨0, by omega⟩]
    convert genericFields_exp_lower caps decode hm selected opponent eta theta heta htheta past field ⟨0, by omega⟩ using 1
    congr 1
    ring
  · rw [partition_totalMass_labels _ _ hp]
    calc
      _ ≤ ∑ _code : Fin (caps field + 1), (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro code _
        rw [genericBlocks_refines caps decode hm selected opponent eta theta past field code]
        exact genericFields_le_one caps decode hm selected opponent eta theta heta htheta past field code
      _ = _ := by simp

def genericLeaf {α : Type*} {m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (field : Fin m) : ProposalLeaf where
  cap := caps field
  blocks := genericBlocks caps decode selected opponent eta theta past field
  partition := genericBlocks_partition caps decode selected opponent eta theta past field
  positive := genericBlocks_positive caps decode selected opponent eta theta heta htheta past field
  decode := decode field
  monotone := hm field

end ImplicitLeafCounts
end Blotto
