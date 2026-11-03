import Blotto.GeneralPaperEqualRealDescription

/-! Scan the already materialized doubled rounded values. One stored load,
comparison and selected continuation per field; the original rounding and
the length array are never rebuilt when selecting the heavy boundary. -/
namespace Blotto.GeneralPaperEqualRealBoundaryScan
set_option autoImplicit false
set_option maxHeartbeats 1600000

def scan {n : ℕ} (lengths : FixedArrayTable n ℚ) : List (Fin n) → Option (Fin n) × ℕ
  | [] => (none, 8)
  | j :: rest =>
    if 1 ≤ lengths.read j then (some j, 16)
    else let child := scan lengths rest; (child.1, child.2 + 16)

theorem data {n : ℕ} (lengths : FixedArrayTable n ℚ) (items : List (Fin n)) :
    (scan lengths items).1 = items.find? (fun j => decide (1 ≤ lengths.read j)) := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
    by_cases h : 1 ≤ lengths.read j <;> simp [scan, h, ih]

theorem work {n : ℕ} (lengths : FixedArrayTable n ℚ) (items : List (Fin n)) :
    (scan lengths items).2 ≤ 16 * items.length + 8 := by
  induction items with
  | nil => rfl
  | cons j rest ih => simp only [scan, List.length_cons]; split_ifs <;> omega

def run {n : ℕ} (lengths : FixedArrayTable n ℚ) : Option (Fin n) × ℕ :=
  let ids := GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size
  let actual := scan lengths ids
  (actual.1, actual.2 + 8 * (lengths.data.size + 1) + 16)

theorem some_heavy {n : ℕ} (lengths : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j, lengths.read j = 2 * v.weight j) (chosen : Fin n) (h : (run lengths).1 = some chosen) :
    (1 / 2 : ℚ) ≤ v.weight chosen := by
  change (scan lengths (GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size)).1 = _ at h
  rw [data, GeneralPaperEqualRouteConstruction.indices_eq] at h
  have hh := of_decide_eq_true (List.find?_some (p := fun j => decide (1 ≤ lengths.read j)) h)
  rw [hv] at hh
  linarith only [hh]

theorem none_small {n : ℕ} (lengths : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j, lengths.read j = 2 * v.weight j) (h : (run lengths).1 = none) :
    ∀ j, 2 * v.weight j ≤ 1 := by
  change (scan lengths (GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size)).1 = _ at h
  rw [data, GeneralPaperEqualRouteConstruction.indices_eq] at h
  simp only [List.find?_eq_none, List.mem_finRange, forall_const, decide_eq_true_eq, not_le] at h
  intro j
  exact (hv j ▸ h j).le

theorem run_work {n : ℕ} (lengths : FixedArrayTable n ℚ) : (run lengths).2 ≤ 32 * (n + 1) := by
  have h := work lengths (GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size)
  rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange] at h
  dsimp only [run]
  rw [GeneralPaperEqualRouteConstruction.indices_eq, lengths.size]
  omega

def vertex {n : ℕ} (budget : ℚ) (chosen : Fin n) : RationalResourceArray n × ℕ :=
  let actual := PaperIndexedArrayConstruction.run (fun _ => 1) 1
    (fun j : Fin n => ((if j = chosen then budget else 0), 8))
  (⟨actual.1.data, actual.1.size⟩, actual.2 + 32)

theorem vertex_data {n : ℕ} (budget : ℚ) (chosen : Fin n) :
    (vertex budget chosen).1.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen := by
  funext j
  change (((PaperIndexedArrayConstruction.run (fun _ => 1) 1
    (fun j : Fin n => ((if j = chosen then budget else 0), 8))).1.read j : ℚ) : ℝ) = _
  rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
  by_cases h : j = chosen <;> simp only [PureBoundaryEquilibria.vertex, h, ite_true, ite_false, Rat.cast_zero]

theorem vertex_work {n : ℕ} (budget : ℚ) (chosen : Fin n) : (vertex budget chosen).2 ≤ 64 * (n + 1) := by
  have h := GeneralPaperRealSegmentCompiler.array_work
    (fun j : Fin n => ((if j = chosen then budget else 0), 8)) 8 (fun _ => le_rfl)
  dsimp only [vertex]
  omega

end Blotto.GeneralPaperEqualRealBoundaryScan
