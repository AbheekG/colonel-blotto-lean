import Blotto.GeneralPaperEqualRealRoutes

/-! Real-model positive compaction reads stored weights, filters labels and
copies weight/endpoint-row references. It constructs no common denominator,
integer count, rejection width or Boolean word. -/
namespace Blotto.GeneralPaperEqualRealCompaction
open GeneralPaperPositiveSegmentCompaction (compact count labels)
open GeneralPaperPreparedPositiveLabels (Selection)
open GeneralPaperRealSegmentCompiler (array_work)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def scan {r : ℕ} (weights : FixedArrayTable r ℚ) : List (Fin r) → List (Fin r) × ℕ
  | [] => ([], 8)
  | j :: rest =>
    let positive := 0 < weights.read j
    let child := scan weights rest
    (if positive then j :: child.1 else child.1, child.2 + 16)

theorem scan_data {r : ℕ} (weights : FixedArrayTable r ℚ) (items : List (Fin r)) :
    (scan weights items).1 = items.filter (fun j => decide (0 < weights.read j)) := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
    simp only [scan, List.filter_cons, ih, decide_eq_true_eq]

theorem scan_work {r : ℕ} (weights : FixedArrayTable r ℚ) (items : List (Fin r)) :
    (scan weights items).2 = 16 * items.length + 8 := by
  induction items with
  | nil => rfl
  | cons j rest ih => simp only [scan, ih, List.length_cons]; omega

def select {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) : Selection l × ℕ :=
  let ids := GeneralPaperEqualRouteConstruction.indices p.weights.data.size p.weights.size
  let actual := scan p.weights ids
  let h : actual.1 = labels l := by
    rw [scan_data]
    dsimp only [ids]
    rw [GeneralPaperEqualRouteConstruction.indices_eq]
    simp only [labels, p.weight_correct]
  (⟨actual.1, h, actual.1.length, rfl⟩,
    actual.2 + 16 * (p.weights.data.size + actual.1.length + 1) + 32)

theorem select_work {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) :
    (select p).2 ≤ 64 * (r + 1) := by
  have h := scan_work p.weights (GeneralPaperEqualRouteConstruction.indices p.weights.data.size p.weights.size)
  have hc : (scan p.weights (GeneralPaperEqualRouteConstruction.indices p.weights.data.size p.weights.size)).1.length ≤ r := by
    rw [scan_data, GeneralPaperEqualRouteConstruction.indices_eq]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := r))
  rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange] at h
  rw [GeneralPaperEqualRouteConstruction.indices_eq] at hc
  dsimp only [select]
  rw [GeneralPaperEqualRouteConstruction.indices_eq, p.weights.size]
  omega

def make {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) (s : Selection l) :
    PreparedSegmentDescriptor (compact l) × ℕ :=
  let itemWork := fun i : Fin (count l) => 8 * (i.val + 1) + 16
  let weights := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => (p.weights.read (s.read i), itemWork i))
  let left := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => (p.left.read (s.read i), itemWork i))
  let right := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => (p.right.read (s.read i), itemWork i))
  let descriptor : PreparedSegmentDescriptor (compact l) :=
    ⟨weights.1, left.1, right.1,
      (by intro i; rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn,
          GeneralPaperPreparedPositiveLabels.read_eq, p.weight_correct]; rfl),
      (by intro i j; rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn,
          GeneralPaperPreparedPositiveLabels.read_eq, p.left_correct]; rfl),
      (by intro i j; rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn,
          GeneralPaperPreparedPositiveLabels.read_eq, p.right_correct]; rfl)⟩
  (descriptor, weights.2 + left.2 + right.2 + 128)

theorem make_work {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) (s : Selection l) :
    (make p s).2 ≤ 24 * r ^ 2 + 198 * r + 182 := by
  have hc : count l ≤ r := by
    rw [← GeneralPaperPreparedPositiveLabels.size_eq s]
    exact GeneralPaperPreparedPositiveLabels.size_le s
  have hi (i : Fin (count l)) : 8 * (i.val + 1) + 16 ≤ 8 * r + 24 := by omega
  have hw := array_work (fun i : Fin (count l) => (p.weights.read (s.read i), 8 * (i.val + 1) + 16)) (8 * r + 24) hi
  have hp := array_work (fun i : Fin (count l) => (p.left.read (s.read i), 8 * (i.val + 1) + 16)) (8 * r + 24) hi
  have hq := array_work (fun i : Fin (count l) => (p.right.read (s.read i), 8 * (i.val + 1) + 16)) (8 * r + 24) hi
  have hScale := Nat.mul_le_mul_right (8 * r + 24 + 42) hc
  dsimp only [make]
  nlinarith only [hw, hp, hq, hScale]

def run {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) :
    PreparedSegmentDescriptor (compact l) × ℕ :=
  let chosen := select p
  let made := make p chosen.1
  (made.1, chosen.2 + made.2 + 64)

theorem data {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) :
    (run p).1 = PreparedSegmentDescriptor.prepare (compact l) := GeneralPaperSegmentExpressionCompiler.unique _ _

theorem work {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) :
    (run p).2 ≤ 512 * (r + 1) ^ 2 := by
  have hs := select_work p
  have hm := make_work p (select p).1
  dsimp only [run]
  nlinarith only [hs, hm, Nat.zero_le (r ^ 2), Nat.zero_le r]

end Blotto.GeneralPaperEqualRealCompaction
