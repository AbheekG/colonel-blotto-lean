import Blotto.GeneralPaperEqualInitialPrefixCapacity

/-! All label cells actually constructed by next-fit cons/reversal operations.
Persistent list tails share a linear label pool; recursive activations own
references, not copies of their complete list tails. Outer result nodes and
the materialized group array are conservatively reserved alongside the pool. -/
namespace Blotto.GeneralPaperPackingAllocationLifetime
open GeneralPaperEqualPackingExecution (scan)
open GeneralPaperEncodedScalarStorage (natBits fields listFootprint)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def labelCells {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ) : List (Fin n) → ℚ → List (Fin n) → ℕ
  | current, _, [] => current.length
  | current, s, x :: rest =>
      if s + values.read x ≤ B then 1 + labelCells values B (x :: current) (s + values.read x) rest
      else current.length + 1 + labelCells values B [x] (values.read x) rest

theorem label_cells_exact {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ)
    (current rest : List (Fin n)) (s : ℚ) :
    labelCells values B current s rest = 2 * rest.length + current.length := by
  induction rest generalizing current s with
  | nil => simp only [labelCells, List.length_nil, Nat.mul_zero, Nat.zero_add]
  | cons x rest ih =>
    rw [labelCells]
    split_ifs <;> rw [ih] <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem group_nodes {n : ℕ} (model : RationalCostModel) (A P : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (current rest : List (Fin n)) (s : ℚ) :
    (scan model A P values B current s rest).1.length ≤ rest.length + 1 := by
  induction rest generalizing current s with
  | nil => simp only [scan, List.length_nil, List.length_singleton, Nat.zero_add, le_rfl]
  | cons x rest ih =>
    rw [scan]
    dsimp only
    split_ifs
    · exact (ih _ _).trans (by simp only [List.length_cons]; omega)
    · simpa only [List.length_cons] using Nat.add_le_add_right (ih [x] (values.read x)) 1

def pool {n : ℕ} (model : RationalCostModel) (A P : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (current rest : List (Fin n)) (s : ℚ) : ℕ :=
  (current.length + rest.length + labelCells values B current s rest + 1) * (1 + binaryWordWidth n + 2 * A) +
    (scan model A P values B current s rest).1.length * (32 * A) + 64 * A

def poolProfile (A n : ℕ) : ℕ := (3 * n + 1) * (1 + binaryWordWidth n + 2 * A) + (n + 1) * (32 * A) + 64 * A

theorem pool_bound {n : ℕ} (model : RationalCostModel) (A P : ℕ) (values : FixedArrayTable n ℚ) (B : ℚ)
    (current rest : List (Fin n)) (s : ℚ) (h : current.length + rest.length ≤ n) :
    pool model A P values B current rest s ≤ poolProfile A n := by
  have hCells : current.length + rest.length + labelCells values B current s rest + 1 ≤ 3 * n + 1 := by
    rw [label_cells_exact]
    omega
  have hGroups := (group_nodes model A P values B current rest s).trans (by omega : rest.length + 1 ≤ n + 1)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_right _ hCells) (Nat.mul_le_mul_right _ hGroups)) _

def indicesLive (A n cursor : ℕ) : ℕ :=
  listFootprint A (fun i => natBits i.val) ((List.finRange n).take cursor) +
    GeneralPaperPositiveSelectionLifetime.traversalFrames A n (GeneralPaperEqualRouteConstruction.indicesWork A n) + fields A [n, cursor] + 64 * A

def indicesProfile (A n : ℕ) : ℕ :=
  GeneralPaperPositiveScanLifetime.labelProfile A n n +
    (n + 1) * GeneralPaperIndexedArrayLifetime.frame A n (GeneralPaperEqualRouteConstruction.indicesWork A n) +
    2 * (natBits (n + 1) + A) + 96 * A

theorem indices_bound (A n cursor : ℕ) (h : cursor ≤ n) : indicesLive A n cursor ≤ indicesProfile A n := by
  have hList := GeneralPaperPositiveScanLifetime.labels_bound A ((List.finRange n).take cursor) n (by
    exact (List.length_take_le ..).trans h)
  have hFrames := GeneralPaperPositiveSelectionLifetime.traversal_bound A n
    (GeneralPaperEqualRouteConstruction.indicesWork A n) _ le_rfl
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + 1) [n, cursor] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega)
  change fields A _ ≤ 2 * (natBits (n + 1) + A) + 32 * A at hFields
  unfold indicesLive indicesProfile
  omega

end Blotto.GeneralPaperPackingAllocationLifetime
