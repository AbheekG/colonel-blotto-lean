import Blotto.RationalOrderCell

/-! Actual aggregated matrix entries of the signed cell are zero or ±1.
Repeated order anchors cancel; distinct tuple fields cannot create repeated
same-sign coefficients. The integer row-l1 bound in RationalOrderCell already
handles all cancellations and supplies the determinant envelope. -/

namespace Blotto.RationalOrderCellCoefficients
open RationalOrderCell
open scoped BigOperators Classical

theorem coefficient_append {d : Type*} [DecidableEq d] (first second : List (d × ℤ)) (coordinate : d) :
    coefficientTerms (first ++ second) coordinate = coefficientTerms first coordinate + coefficientTerms second coordinate := by
  simp [coefficientTerms,List.map_append,List.sum_append]

theorem sum_neg_int {d : Type*} (terms : List d) (f : d → ℤ) :
    (terms.map (fun term => -f term)).sum = -(terms.map f).sum := by
  induction terms with
  | nil => simp
  | cons first rest ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem coefficient_neg_map {d : Type*} [DecidableEq d] (terms : List (d × ℤ)) (coordinate : d) :
    coefficientTerms (terms.map (fun term => (term.1,-term.2))) coordinate = -coefficientTerms terms coordinate := by
  unfold coefficientTerms
  simp only [List.map_map,Function.comp_def]
  have hFun : (fun term : d × ℤ => if term.1 = coordinate then -term.2 else 0) =
      fun term => -(if term.1 = coordinate then term.2 else 0) := by
    funext term
    split <;> simp
  rw [hFun,sum_neg_int]

theorem coefficient_neg {d : Type*} [DecidableEq d] (row : LinearRow d) (coordinate : d) :
    row.neg.coefficient coordinate = -row.coefficient coordinate :=
  coefficient_neg_map row.terms coordinate

theorem ref_coefficient_bounds {m K : ℕ} (r : Reference m K) (coordinate : Variable m K) :
    0 ≤ coefficientTerms (refTerms r) coordinate ∧ coefficientTerms (refTerms r) coordinate ≤ 1 := by
  cases r with
  | none => simp [refTerms,coefficientTerms]
  | some r => cases r with
    | none => simp [refTerms,coefficientTerms]
    | some v =>
      by_cases h : v = coordinate <;> simp [refTerms,coefficientTerms,h]

theorem tuple_coefficient_other_field {m K : ℕ} (field : Fin m) (label : Fin K)
    (coordinate : Variable m K) (hField : field ≠ coordinate.1) :
    coefficientTerms (refTerms (tupleReference field label)) coordinate = 0 := by
  unfold tupleReference reference
  by_cases hZero : label.val = 0
  · simp [hZero,refTerms,coefficientTerms]
  · have hOne : label.val ≠ K := Nat.ne_of_lt label.isLt
    simp only [hZero,hOne,dite_false,refTerms,coefficientTerms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    have hPair : ((field,⟨label.val - 1,by have hl := label.isLt; omega⟩) : Variable m K) ≠ coordinate := by
      intro h
      exact hField (congrArg Prod.fst h)
    exact ite_eq_right hPair

theorem raw_order_coefficient_bounds {m K : ℕ} (budgets : Fin 2 → ℚ)
    (field : Fin m) (left right : Fin (K + 1)) (coordinate : Variable m K) :
    -1 ≤ (rawRow budgets (.inl (field,left,right))).coefficient coordinate ∧
      (rawRow budgets (.inl (field,left,right))).coefficient coordinate ≤ 1 := by
  have hl := ref_coefficient_bounds (reference field left) coordinate
  have hr := ref_coefficient_bounds (reference field right) coordinate
  change -1 ≤ coefficientTerms (_ ++ _) coordinate ∧ coefficientTerms (_ ++ _) coordinate ≤ 1
  rw [coefficient_append,coefficient_neg_map]
  omega

theorem raw_sum_coefficient_bounds {m K : ℕ} (budgets : Fin 2 → ℚ)
    (labels : Fin m → Fin K) (budget : Fin 2) (coordinate : Variable m K) :
    -1 ≤ (rawRow budgets (.inr (labels,budget))).coefficient coordinate ∧
      (rawRow budgets (.inr (labels,budget))).coefficient coordinate ≤ 1 := by
  have hCoeff : (rawRow budgets (.inr (labels,budget))).coefficient coordinate =
      ∑ field, coefficientTerms (refTerms (tupleReference field (labels field))) coordinate := by
    unfold rawRow LinearRow.coefficient coefficientTerms
    rw [List.map_flatten,List.sum_flatten]
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
  have hSingle : (∑ field, coefficientTerms (refTerms (tupleReference field (labels field))) coordinate) =
      coefficientTerms (refTerms (tupleReference coordinate.1 (labels coordinate.1))) coordinate := by
    apply Finset.sum_eq_single coordinate.1
    · intro field _ hOther
      exact tuple_coefficient_other_field field (labels field) coordinate hOther
    · intro hMissing
      exact False.elim (hMissing (Finset.mem_univ _))
  rw [hCoeff,hSingle]
  have h := ref_coefficient_bounds (tupleReference coordinate.1 (labels coordinate.1)) coordinate
  exact ⟨by omega,h.2⟩

theorem raw_coefficient_bounds {m K : ℕ} (budgets : Fin 2 → ℚ) (check : Check m K) (coordinate : Variable m K) :
    -1 ≤ (rawRow budgets check).coefficient coordinate ∧ (rawRow budgets check).coefficient coordinate ≤ 1 := by
  cases check with
  | inl order => exact raw_order_coefficient_bounds budgets order.1 order.2.1 order.2.2 coordinate
  | inr summed => exact raw_sum_coefficient_bounds budgets summed.1 summed.2 coordinate

theorem lift_coefficient_none {m K : ℕ} (row : LinearRow (Variable m K)) : (liftRow row).coefficient none = 0 := by
  simp [liftRow,LinearRow.coefficient,coefficientTerms,List.map_map,Function.comp_def]

theorem lift_coefficient_some {m K : ℕ} (row : LinearRow (Variable m K)) (coordinate : Variable m K) :
    (liftRow row).coefficient (some coordinate) = row.coefficient coordinate := by
  simp [liftRow,LinearRow.coefficient,coefficientTerms,List.map_map,Function.comp_def]

theorem margin_coefficient_none {m K : ℕ} (row : LinearRow (Variable m K)) : (withMargin row).coefficient none = 1 := by
  change coefficientTerms ((liftRow row).terms ++ [(none,1)]) none = _
  rw [coefficient_append]
  change (liftRow row).coefficient none + _ = _
  simp [lift_coefficient_none,coefficientTerms]

theorem margin_coefficient_some {m K : ℕ} (row : LinearRow (Variable m K)) (coordinate : Variable m K) :
    (withMargin row).coefficient (some coordinate) = row.coefficient coordinate := by
  change coefficientTerms ((liftRow row).terms ++ [(none,1)]) (some coordinate) = _
  rw [coefficient_append]
  change (liftRow row).coefficient (some coordinate) + _ = _
  simp [lift_coefficient_some,coefficientTerms]

theorem signed_coefficient_bounds {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (check : Check m K) (half : Bool) (coordinate : Coordinate m K) :
    -1 ≤ (signedRow original (rawRow budgets check) half).coefficient coordinate ∧
      (signedRow original (rawRow budgets check) half).coefficient coordinate ≤ 1 := by
  cases coordinate with
  | none =>
    unfold signedRow
    split
    · simp [margin_coefficient_none]
    · split
      · simp [margin_coefficient_none]
      · cases half <;> simp [lift_coefficient_none]
  | some coordinate =>
    have h := raw_coefficient_bounds budgets check coordinate
    unfold signedRow
    split
    · simpa only [margin_coefficient_some] using h
    · split
      · simp only [margin_coefficient_some,coefficient_neg]; omega
      · cases half <;> simp only [Bool.false_eq_true,ite_false,ite_true,lift_coefficient_some,coefficient_neg] <;> omega

theorem constraint_coefficient_bounds {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (row : CellRow m K) (coordinate : Coordinate m K) :
    -1 ≤ (constraint budgets original row).coefficient coordinate ∧
      (constraint budgets original row).coefficient coordinate ≤ 1 := by
  cases row with
  | inl bound =>
    obtain ⟨stored,upper⟩ := bound
    by_cases h : stored = coordinate <;> cases upper <;> simp [constraint,boxRow,LinearRow.coefficient,coefficientTerms,h]
  | inr signed => exact signed_coefficient_bounds budgets original signed.1 signed.2 coordinate

theorem constraint_coefficient_unit {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (row : CellRow m K) (coordinate : Coordinate m K) :
    (constraint budgets original row).coefficient coordinate = -1 ∨
      (constraint budgets original row).coefficient coordinate = 0 ∨
      (constraint budgets original row).coefficient coordinate = 1 := by
  have h := constraint_coefficient_bounds budgets original row coordinate
  omega

end Blotto.RationalOrderCellCoefficients
