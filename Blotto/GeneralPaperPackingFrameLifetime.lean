import Blotto.GeneralPaperPackingAllocationLifetime

/-! Recursive packing frames keep scalar data/scratch and references into
one label pool. Local reached charges pay for scalar storage once; only
short work-counter words are reserved per pending frame. -/
namespace Blotto.GeneralPaperPackingFrameLifetime
open GeneralPaperEqualPackingExecution (scan unit)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def body {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ) (B s : ℚ) (x : Fin n) : ℕ :=
  4 * (rationalWordWidth (values.read x) + model.rat (RationalExpression.pairWidth s (values.read x)) +
    model.rat (RationalExpression.pairWidth (s + values.read x) B) + 2 * A)

def nextCurrent {n : ℕ} (values : FixedArrayTable n ℚ) (B s : ℚ) (current : List (Fin n)) (x : Fin n) : List (Fin n) :=
  if s + values.read x ≤ B then x :: current else [x]

def nextSum {n : ℕ} (values : FixedArrayTable n ℚ) (B s : ℚ) (x : Fin n) : ℚ :=
  if s + values.read x ≤ B then s + values.read x else values.read x

def headPrice {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ)
    (B s : ℚ) (current : List (Fin n)) (x : Fin n) : ℕ :=
  body values model A B s x + if s + values.read x ≤ B then unit A n else
    4 * (rationalWordWidth s + (current.length + 2) * A) + unit A n * (current.length + 2)

theorem price_shape {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ)
    (B s : ℚ) (current rest : List (Fin n)) (x : Fin n) :
    (scan model A (unit A n) values B current s (x :: rest)).2 = headPrice values model A B s current x +
      (scan model A (unit A n) values B (nextCurrent values B s current x) (nextSum values B s x) rest).2 := by
  rw [scan]
  simp only [headPrice, body, nextCurrent, nextSum]
  split_ifs <;> omega

theorem head_bounds {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ)
    (B s : ℚ) (current : List (Fin n)) (x : Fin n) :
    body values model A B s x ≤ headPrice values model A B s current x ∧ unit A n ≤ headPrice values model A B s current x := by
  have hMul := Nat.mul_le_mul_left (unit A n) (show 1 ≤ current.length + 2 by omega)
  simp only [Nat.mul_one] at hMul
  unfold headPrice
  split_ifs <;> omega

def scalarScratch {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (B s : ℚ) (x : Fin n) : ℕ :=
  rationalWordWidth s + rationalWordWidth (values.read x) + rationalWordWidth (s + values.read x) + rationalWordWidth B +
    2 * model.rat (RationalExpression.pairWidth s (values.read x)) + 2 * model.rat (RationalExpression.pairWidth (s + values.read x) B)

theorem scalar_bound {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ) (B s : ℚ) (x : Fin n) :
    scalarScratch values model B s x ≤ body values model A B s x := by
  have hS := (le_max_left (rationalWordWidth s) (rationalWordWidth (values.read x))).trans
    (model.word_le (RationalExpression.pairWidth s (values.read x)))
  have hNext := (le_max_left (rationalWordWidth (s + values.read x)) (rationalWordWidth B)).trans
    (model.word_le (RationalExpression.pairWidth (s + values.read x) B))
  have hB := (le_max_right (rationalWordWidth (s + values.read x)) (rationalWordWidth B)).trans
    (model.word_le (RationalExpression.pairWidth (s + values.read x) B))
  unfold scalarScratch body
  omega

def frameProfile (A n F : ℕ) : ℕ := 10 * (natBits (n + F + unit A n + 1) + A) + 32 * A

def baseFoot {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ) (B s : ℚ) (current : List (Fin n)) : ℕ :=
  let actual := scan model A (unit A n) values B current s []
  rationalWordWidth s + actual.2 + fields A [n, current.length, unit A n, actual.2] + 256 * A

def stepFoot {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ)
    (B s : ℚ) (current rest : List (Fin n)) (x : Fin n) : ℕ :=
  let H := headPrice values model A B s current x
  let child := scan model A (unit A n) values B (nextCurrent values B s current x) (nextSum values B s x) rest
  let actual := scan model A (unit A n) values B current s (x :: rest)
  scalarScratch values model B s x + H +
    fields A [n, current.length, rest.length, x.val, unit A n, body values model A B s x, H, child.2, H + child.2, actual.2] + 256 * A

theorem base_bound {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A F : ℕ)
    (B s : ℚ) (current : List (Fin n)) (hL : current.length ≤ n)
    (hF : (scan model A (unit A n) values B current s []).2 ≤ F) :
    baseFoot values model A B s current ≤ 8 * (scan model A (unit A n) values B current s []).2 + frameProfile A n F := by
  let C := (scan model A (unit A n) values B current s []).2
  have hC : C = 4 * (rationalWordWidth s + (current.length + 2) * A) + unit A n * (current.length + 1) := rfl
  have hMul := Nat.mul_le_mul_left (unit A n) (show 1 ≤ current.length + 1 by omega)
  simp only [Nat.mul_one] at hMul
  have hUnit : 64 * A + 64 ≤ unit A n := by unfold unit; omega
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + F + unit A n + 1)
    [n, current.length, unit A n, C] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 4 * (natBits (n + F + unit A n + 1) + A) + 32 * A at hFields
  change rationalWordWidth s + C + fields A [n, current.length, unit A n, C] + 256 * A ≤ 8 * C + frameProfile A n F
  unfold frameProfile
  omega

theorem step_bound {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A F : ℕ)
    (B s : ℚ) (current rest : List (Fin n)) (x : Fin n) (hL : current.length + (x :: rest).length ≤ n)
    (hF : (scan model A (unit A n) values B current s (x :: rest)).2 ≤ F) :
    stepFoot values model A B s current rest x ≤ 8 * headPrice values model A B s current x + frameProfile A n F := by
  let H := headPrice values model A B s current x
  let child := scan model A (unit A n) values B (nextCurrent values B s current x) (nextSum values B s x) rest
  let C := (scan model A (unit A n) values B current s (x :: rest)).2
  have hC : C = H + child.2 := price_shape values model A B s current rest x
  simp only [List.length_cons] at hL
  have hHead := head_bounds values model A B s current x
  have hScalar := scalar_bound values model A B s x
  have hUnit : 64 * A + 64 ≤ unit A n := by unfold unit; omega
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + F + unit A n + 1)
    [n, current.length, rest.length, x.val, unit A n, body values model A B s x, H, child.2, H + child.2, C] (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 10 * (natBits (n + F + unit A n + 1) + A) + 32 * A at hFields
  change scalarScratch values model B s x + H +
    fields A [n, current.length, rest.length, x.val, unit A n, body values model A B s x, H, child.2, H + child.2, C] + 256 * A ≤ 8 * H + frameProfile A n F
  unfold frameProfile
  omega

def frames {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ) (B : ℚ) :
    List (Fin n) → ℚ → List (Fin n) → ℕ
  | current, s, [] => baseFoot values model A B s current
  | current, s, x :: rest => stepFoot values model A B s current rest x +
      frames values model A B (nextCurrent values B s current x) (nextSum values B s x) rest

theorem frames_bound {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A F : ℕ) (B s : ℚ)
    (current rest : List (Fin n)) (hL : current.length + rest.length ≤ n)
    (hF : (scan model A (unit A n) values B current s rest).2 ≤ F) :
    frames values model A B current s rest ≤ 8 * (scan model A (unit A n) values B current s rest).2 +
      (rest.length + 1) * frameProfile A n F := by
  induction rest generalizing current s with
  | nil => simpa only [frames, List.length_nil, Nat.add_zero, Nat.zero_add, one_mul] using base_bound values model A F B s current hL hF
  | cons x rest ih =>
    have hShape := price_shape values model A B s current rest x
    have hStep := step_bound values model A F B s current rest x hL hF
    have hChild : (scan model A (unit A n) values B (nextCurrent values B s current x) (nextSum values B s x) rest).2 ≤ F := by omega
    have hSize : (nextCurrent values B s current x).length + rest.length ≤ n := by
      unfold nextCurrent
      split_ifs <;> simp only [List.length_cons, List.length_nil] at * <;> omega
    have hRest := ih (nextSum values B s x) (nextCurrent values B s current x) hSize hChild
    simp only [frames, List.length_cons]
    nlinarith only [hStep, hRest, hShape]

end Blotto.GeneralPaperPackingFrameLifetime
