import Blotto.PreparedGroupOutput
import Blotto.RationalHeightBudget
import Blotto.RationalPRGResourceBitWidth
import Blotto.RationalExpressionWordWidth

/-! Cached group coefficients and actual array emission have height bounds
independent of field count. Group totals retain the input denominator lattice;
no reciprocal lower bound on a positive total is needed. -/

namespace Blotto

namespace RationalProportionalGroups

def FieldsHeight {n m : ℕ} (G : RationalProportionalGroups n m) (s : ℕ) : Prop :=
  (∀ j, RationalHeight (G.length j) s) ∧ ∀ g, RationalHeight (G.total g) s

theorem total_on_lattice {n m : ℕ} (G : RationalProportionalGroups n m) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (G.length j)) (g : Fin m) : OnRationalLattice D (G.total g) := by
  rw [total, G.total_eq]
  exact OnRationalLattice.list_sum G.length (G.members g) (fun j _ => hL j)

theorem fieldsHeight_of_lattice {n m : ℕ} (G : RationalProportionalGroups n m) (D : ℕ) (hD : 0 < D)
    (hL : ∀ j, OnRationalLattice D (G.length j)) (hL1 : ∀ j, G.length j ≤ 1)
    (hT1 : ∀ g, G.total g ≤ 1) : G.FieldsHeight (1 + 2 * binaryWordWidth D) := by
  constructor
  · intro j
    exact (rationalHeight_of_wordWidth (G.length j)).mono
      (rationalWordWidth_lattice_bound hD (hL j) ⟨le_of_lt (G.length_pos j), hL1 j⟩)
  · intro g
    exact (rationalHeight_of_wordWidth (G.total g)).mono
      (rationalWordWidth_lattice_bound hD (G.total_on_lattice D hL g) ⟨le_of_lt (G.total_pos g), hT1 g⟩)

theorem FieldsHeight.ratio {n m : ℕ} {G : RationalProportionalGroups n m} {s : ℕ} (h : G.FieldsHeight s)
    (j : Fin n) (g : Fin m) : RationalHeight (G.length j / G.total g) (expressionHeightBudget s 1) := by
  have hL : RationalHeight (G.length j) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.1 j
  have hT : RationalHeight (G.total g) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2 g
  exact hL.div_level hT

theorem ratio_reduced_bounds_lattice {n m : ℕ} (G : RationalProportionalGroups n m) (D : ℕ) (hD : 0 < D)
    (hL : ∀ j, OnRationalLattice D (G.length j)) (hL1 : ∀ j, G.length j ≤ 1)
    (hT1 : ∀ g, G.total g ≤ 1) (j : Fin n) (g : Fin m) :
    (G.length j / G.total g).num.natAbs ≤ D ∧ (G.length j / G.total g).den ≤ D := by
  let a := latticeNumerator D (G.length j)
  let b := latticeNumerator D (G.total g)
  have hTotal := G.total_on_lattice D hL g
  have hA := latticeNumerator_bounds (hL j) ⟨le_of_lt (G.length_pos j), hL1 j⟩
  have hB := latticeNumerator_bounds hTotal ⟨le_of_lt (G.total_pos g), hT1 g⟩
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hBposQ : (0 : ℚ) < (b : ℚ) := by
    rw [latticeNumerator_cast_eq_mul hTotal]
    exact mul_pos (G.total_pos g) hDq
  have hBpos : 0 < b := by exact_mod_cast hBposQ
  have hBcast : (b.toNat : ℚ) = (b : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hBpos.le
  have hBnPos : 0 < b.toNat := by
    have he : (0 : ℤ) < (b.toNat : ℤ) := by rw [Int.toNat_of_nonneg hBpos.le]; exact hBpos
    exact_mod_cast he
  have hAn : a.natAbs ≤ D := by
    have he : (a.natAbs : ℤ) ≤ (D : ℤ) := by rw [Int.natAbs_of_nonneg hA.1]; exact hA.2
    exact_mod_cast he
  have hBn : b.toNat ≤ D := by
    have he : (b.toNat : ℤ) ≤ (D : ℤ) := by rw [Int.toNat_of_nonneg hBpos.le]; exact hB.2
    exact_mod_cast he
  have hRatio : (a : ℚ) / b.toNat = G.length j / G.total g := by
    rw [hBcast, latticeNumerator_cast_eq_mul (hL j), latticeNumerator_cast_eq_mul hTotal]
    field_simp [ne_of_gt hDq, ne_of_gt (G.total_pos g)]
  have hReduced := reduced_fraction_bounds a b.toNat hBnPos
  rw [hRatio] at hReduced
  exact ⟨hReduced.1.trans hAn, hReduced.2.trans hBn⟩

theorem ratio_height_lattice {n m : ℕ} (G : RationalProportionalGroups n m) (D : ℕ) (hD : 0 < D)
    (hL : ∀ j, OnRationalLattice D (G.length j)) (hL1 : ∀ j, G.length j ≤ 1)
    (hT1 : ∀ g, G.total g ≤ 1) (j : Fin n) (g : Fin m) :
    RationalHeight (G.length j / G.total g) (binaryWordWidth D) := by
  have h := G.ratio_reduced_bounds_lattice D hD hL hL1 hT1 j g
  exact ⟨h.1.trans_lt (lt_pow_binaryWordWidth D), h.2.trans_lt (lt_pow_binaryWordWidth D)⟩

end RationalProportionalGroups

namespace PreparedGroupOutput

theorem coefficient_height_lattice {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (D : ℕ) (hD : 0 < D) (hL : ∀ j, OnRationalLattice D (G.length j))
    (hL1 : ∀ j, G.length j ≤ 1) (hT1 : ∀ g, G.total g ≤ 1) (j : Fin n) :
    RationalHeight (p.table.read j).2 (binaryWordWidth D) := by
  classical
  rw [p.correct]
  by_cases he : ∃ g, j ∈ G.members g
  · rcases he with ⟨g, hg⟩
    rw [G.routes_group hg]
    exact G.ratio_height_lattice D hD hL hL1 hT1 j g
  · have hj : ∀ g, j ∉ G.members g := by simpa using he
    rw [G.routes_inactive hj]
    exact (show RationalHeight (0 : ℚ) 1 by norm_num [RationalHeight]).mono (by
      have h := binaryWordWidth_pos D
      omega)

theorem emit_of_coefficient_heights {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (s t : ℕ) (hs : 1 ≤ s) (hCoefficient : ∀ j, RationalHeight (p.table.read j).2 s)
    (y : Fin m → ℚ) (hY : ∀ g, RationalHeight (y g) t) (j : Fin n) :
    RationalHeight ((p.emit y).allocation j) (expressionHeightBudget (max s t) 1) := by
  let w := max s t
  have hw : 1 ≤ w := hs.trans (le_max_left _ _)
  have hC : RationalHeight (p.table.read j).2 (expressionHeightBudget w 0) := by
    simpa only [expressionHeightBudget_zero] using (hCoefficient j).mono (le_max_left _ _)
  have hValues : ∀ g, RationalHeight (y g) (expressionHeightBudget w 0) := by
    intro g
    simpa only [expressionHeightBudget_zero] using (hY g).mono (le_max_right _ _)
  simp only [emit, RationalProportionalGroups.emit, RationalResourceArray.allocation_ofAllocation, FixedArrayTable.read_ofFn]
  cases (p.table.read j).1 with
  | none =>
    exact (show RationalHeight (0 : ℚ) 1 by norm_num [RationalHeight]).mono (hw.trans (expressionHeightBudget_ge_input w 1))
  | some g => exact hC.mul_level (hValues g)

theorem emitMixed_of_coefficient_heights {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (s t : ℕ) (hs : 1 ≤ s) (hCoefficient : ∀ j, RationalHeight (p.table.read j).2 s)
    (pivot : Fin n) (y : Fin (m + 1) → ℚ) (hY : ∀ g, RationalHeight (y g) t) (j : Fin n) :
    RationalHeight ((p.emitMixed pivot y).allocation j) (expressionHeightBudget (max s t) 2) := by
  let w := max s t
  have hw : 1 ≤ w := hs.trans (le_max_left _ _)
  have hBase := p.emit_of_coefficient_heights s t hs hCoefficient (fun g => y g.castSucc) (fun g => hY g.castSucc) j
  rw [p.emit_allocation] at hBase
  have hExtra : RationalHeight (if j = pivot then y (Fin.last m) else 0) (expressionHeightBudget w 1) := by
    by_cases hj : j = pivot
    · rw [ite_eq_left hj]
      exact (hY _).mono ((le_max_right _ _).trans (expressionHeightBudget_ge_input w 1))
    · rw [ite_eq_right hj]
      exact (show RationalHeight (0 : ℚ) 1 by norm_num [RationalHeight]).mono (hw.trans (expressionHeightBudget_ge_input w 1))
  rw [p.emitMixed_allocation, G.emitMixed_allocation_add]
  exact hBase.add_level hExtra

theorem coefficient_height {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (s : ℕ) (hs : 2 ≤ s) (hG : G.FieldsHeight s) (j : Fin n) :
    RationalHeight (p.table.read j).2 (expressionHeightBudget s 1) := by
  classical
  rw [p.correct]
  by_cases he : ∃ g, j ∈ G.members g
  · rcases he with ⟨g, hg⟩
    rw [G.routes_group hg]
    exact hG.ratio j g
  · have hj : ∀ g, j ∉ G.members g := by simpa using he
    rw [G.routes_inactive hj]
    exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 1))

theorem emit_height {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (s t : ℕ) (hs : 2 ≤ s) (hG : G.FieldsHeight s) (y : Fin m → ℚ)
    (hY : ∀ g, RationalHeight (y g) t) (j : Fin n) :
    RationalHeight ((p.emit y).allocation j) (expressionHeightBudget (max (expressionHeightBudget s 1) t) 1) := by
  classical
  let w := max (expressionHeightBudget s 1) t
  have hw : 2 ≤ w := hs.trans ((expressionHeightBudget_ge_input s 1).trans (le_max_left _ _))
  rw [p.emit_allocation]
  by_cases he : ∃ g, j ∈ G.members g
  · rcases he with ⟨g, hg⟩
    rw [G.emit_group hg]
    have hRatio : RationalHeight (G.length j / G.total g) (expressionHeightBudget w 0) := by
      simpa only [expressionHeightBudget_zero] using (hG.ratio j g).mono (le_max_left _ _)
    have hValue : RationalHeight (y g) (expressionHeightBudget w 0) := by
      simpa only [expressionHeightBudget_zero] using (hY g).mono (le_max_right _ _)
    exact hRatio.mul_level hValue
  · have hj : ∀ g, j ∉ G.members g := by simpa using he
    rw [G.emit_inactive hj]
    exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hw.trans (expressionHeightBudget_ge_input w 1))

theorem emitMixed_height {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (s t : ℕ) (hs : 2 ≤ s) (hG : G.FieldsHeight s) (pivot : Fin n) (y : Fin (m + 1) → ℚ)
    (hY : ∀ g, RationalHeight (y g) t) (j : Fin n) :
    RationalHeight ((p.emitMixed pivot y).allocation j) (expressionHeightBudget (max (expressionHeightBudget s 1) t) 2) := by
  let w := max (expressionHeightBudget s 1) t
  have hw : 2 ≤ w := hs.trans ((expressionHeightBudget_ge_input s 1).trans (le_max_left _ _))
  have hBase := p.emit_height s t hs hG (fun g => y g.castSucc) (fun g => hY g.castSucc) j
  rw [p.emit_allocation] at hBase
  have hExtra : RationalHeight (if j = pivot then y (Fin.last m) else 0) (expressionHeightBudget w 1) := by
    by_cases hj : j = pivot
    · rw [ite_eq_left hj]
      exact (hY _).mono ((le_max_right _ _).trans (expressionHeightBudget_ge_input w 1))
    · rw [ite_eq_right hj]
      exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hw.trans (expressionHeightBudget_ge_input w 1))
  rw [p.emitMixed_allocation, G.emitMixed_allocation_add]
  exact hBase.add_level hExtra

end PreparedGroupOutput
end Blotto
