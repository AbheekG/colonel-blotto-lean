import Blotto.GeneralPaperEqualCachedPreparation
import Blotto.RationalPackingBitCost

/-! A fused next-fit packing source for a materialized rational length array.
Each input, tentative sum and child return is computed once. The observer
includes rational copy/arithmetic/comparison, references, list reversal and
control. It does not include construction of the input length array. -/
namespace Blotto.GeneralPaperEqualPackingExecution
set_option autoImplicit false
set_option maxHeartbeats 1200000

def unit (A n : ℕ) : ℕ := 64 * (A + binaryWordWidth (n + 1) + 1)

def scan {n : ℕ} (model : RationalCostModel) (A P : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ) :
    List (Fin n) → ℚ → List (Fin n) → List (List (Fin n) × ℚ) × ℕ
  | current, s, [] =>
      ([(current.reverse, s)], 4 * (rationalWordWidth s + (current.length + 2) * A) + P * (current.length + 1))
  | current, s, x :: rest =>
      let value := values.read x
      let next := s + value
      let body := 4 * (rationalWordWidth value + model.rat (RationalExpression.pairWidth s value) +
        model.rat (RationalExpression.pairWidth next B) + 2 * A)
      if next ≤ B then
        let child := scan model A P values B (x :: current) next rest
        (child.1, body + P + child.2)
      else
        let child := scan model A P values B [x] value rest
        ((current.reverse, s) :: child.1,
          body + 4 * (rationalWordWidth s + (current.length + 2) * A) + P * (current.length + 2) + child.2)

theorem scan_data {n : ℕ} (model : RationalCostModel) (A P : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (current : List (Fin n)) (s : ℚ) (rest : List (Fin n)) :
    (scan model A P values B current s rest).1 = rationalPackSumsAux values.read B current s rest := by
  induction rest generalizing current s with
  | nil => rfl
  | cons x rest ih =>
    rw [scan, rationalPackSumsAux]
    dsimp only
    split_ifs
    · exact ih _ _
    · exact congrArg (List.cons (current.reverse, s)) (ih _ _)

theorem scan_work {n : ℕ} (model : RationalCostModel) (A P : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (current : List (Fin n)) (s : ℚ) (rest : List (Fin n)) :
    (scan model A P values B current s rest).2 =
      4 * RationalPackingCost.scan model A values.read B current s rest +
        P * (2 * rest.length + current.length + (rationalPackSumsAux values.read B current s rest).length) := by
  induction rest generalizing current s with
  | nil => simp only [scan, RationalPackingCost.scan, rationalPackSumsAux, List.length_nil, List.length_singleton]; ring
  | cons x rest ih =>
    rw [scan, RationalPackingCost.scan, rationalPackSumsAux]
    dsimp only
    split_ifs
    · rw [ih]
      simp only [List.length_cons]
      ring
    · rw [ih]
      simp only [List.length_cons, List.length_nil]
      ring

def run {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (items : List (Fin n)) : List (List (Fin n) × ℚ) × ℕ :=
  let P := unit A values.data.size
  match items with
  | [] => ([], P)
  | x :: rest =>
      let value := values.read x
      let child := scan model A P values B [x] value rest
      (child.1, 4 * (rationalWordWidth value + 2 * A) + 2 * P + child.2)

theorem data {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (items : List (Fin n)) : (run model A values B items).1 = rationalPackedGroups values.read B items := by
  cases items with
  | nil => rfl
  | cons x rest => exact scan_data model A _ values B [x] (values.read x) rest

theorem work {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (items : List (Fin n)) :
    (run model A values B items).2 = 4 * RationalPackingCost.packed model A values.read B items +
      unit A n * (2 * items.length + (rationalPackedGroups values.read B items).length + 1) := by
  cases items with
  | nil => simp only [run, values.size, RationalPackingCost.packed, rationalPackedGroups, List.length_nil]; ring
  | cons x rest =>
    simp only [run, values.size, RationalPackingCost.packed, rationalPackedGroups, scan_work,
      List.length_cons, List.length_nil]
    ring

theorem bound {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (D W : ℕ) (hD : 0 < D) (hB : B ≤ 1) (hBW : rationalWordWidth B ≤ W)
    (hW : 3 + 2 * binaryWordWidth D ≤ W) (items : List (Fin n))
    (hItems : ∀ j ∈ items, OnRationalLattice D (values.read j) ∧ 0 ≤ values.read j ∧ values.read j ≤ B)
    (hCount : (rationalPackedGroups values.read B items).length ≤ 3) (hLength : items.length ≤ n) :
    (run model A values B items).2 ≤
      (12 * n + 12) * model.rat W + (12 * n + 24) * A + unit A n * (2 * n + 4) := by
  have h := RationalPackingCost.packed_bound model A values.read B D W hD hB hBW hW items hItems
  have hR := Nat.mul_le_mul_right (model.rat W)
    (show 3 * items.length + (rationalPackedGroups values.read B items).length ≤ 3 * n + 3 by omega)
  have hA := Nat.mul_le_mul_right A
    (show 3 * items.length + 2 * (rationalPackedGroups values.read B items).length ≤ 3 * n + 6 by omega)
  have hP := Nat.mul_le_mul_left (unit A n)
    (show 2 * items.length + (rationalPackedGroups values.read B items).length + 1 ≤ 2 * n + 4 by omega)
  rw [work]
  nlinarith only [h, hR, hA, hP]

end Blotto.GeneralPaperEqualPackingExecution
