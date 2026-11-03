import Blotto.GeneralPaperPreparedPositiveLabels

/-! Compact by selecting stored probabilities and endpoint-row references.
The selected list/size are retained once; no local formula is evaluated.
The paper model stores one reference per endpoint row, without copying it. -/
namespace Blotto.GeneralPaperPreparedSegmentCompaction
open GeneralPaperPreparedPositiveLabels (Selection)
open GeneralPaperPositiveSegmentCompaction (compact count)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000

def readWork (A r i : ℕ) : ℕ := 64 * (i + 1) * (A + binaryWordWidth (r + 1) + 1)

def weightItem {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (s : Selection l) (A : ℕ) (i : Fin (count l)) : ℚ × ℕ :=
  let label := s.read i
  let value := p.weights.read label
  (value, rationalWordWidth value + readWork A p.weights.data.size i.val + 32 * A + 32)

def leftItem {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (s : Selection l) (A : ℕ) (i : Fin (count l)) : FixedArrayTable n ℚ × ℕ :=
  let label := s.read i
  (p.left.read label, readWork A p.weights.data.size i.val + 32 * A + 32)

def rightItem {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (s : Selection l) (A : ℕ) (i : Fin (count l)) : FixedArrayTable n ℚ × ℕ :=
  let label := s.read i
  (p.right.read label, readWork A p.weights.data.size i.val + 32 * A + 32)

def make {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (s : Selection l) (A : ℕ) : PreparedSegmentDescriptor (compact l) × ℕ :=
  let weights := GeneralPaperSizedBitArray.run s.size (GeneralPaperPreparedPositiveLabels.size_eq s) A (weightItem p s A)
  let left := GeneralPaperSizedBitArray.run s.size (GeneralPaperPreparedPositiveLabels.size_eq s) A (leftItem p s A)
  let right := GeneralPaperSizedBitArray.run s.size (GeneralPaperPreparedPositiveLabels.size_eq s) A (rightItem p s A)
  let descriptor : PreparedSegmentDescriptor (compact l) :=
    ⟨weights.1, left.1, right.1,
      (by
        intro i
        dsimp only [weights]
        rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
        dsimp only [weightItem]
        rw [GeneralPaperPreparedPositiveLabels.read_eq, p.weight_correct]
        rfl),
      (by
        intro i j
        dsimp only [left]
        rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
        dsimp only [leftItem]
        rw [GeneralPaperPreparedPositiveLabels.read_eq, p.left_correct]
        rfl),
      (by
        intro i j
        dsimp only [right]
        rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
        dsimp only [rightItem]
        rw [GeneralPaperPreparedPositiveLabels.read_eq, p.right_correct]
        rfl)⟩
  (descriptor, weights.2 + left.2 + right.2 + 64 * A + 64)

theorem make_data {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (s : Selection l) (A : ℕ) : (make p s A).1 = PreparedSegmentDescriptor.prepare (compact l) :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

def run {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) : PreparedSegmentDescriptor (compact l) × ℕ :=
  let chosen := GeneralPaperPreparedPositiveLabels.run p model A
  let made := make p chosen.1 A
  (made.1, chosen.2 + made.2 + 64 * A + 64)

theorem data {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) :
    (run p model A).1 = PreparedSegmentDescriptor.prepare (compact l) :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

def itemBound (A r s : ℕ) : ℕ :=
  1 + 2 * s + 64 * (r + 1) * (A + binaryWordWidth (r + 1) + 1) + 32 * A + 32

theorem item_work {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (chosen : Selection l) (A : ℕ) (h : ∀ i, RationalHeight (l.weight i) s) (i : Fin (count l)) :
    (weightItem p chosen A i).2 ≤ itemBound A r s ∧
      (leftItem p chosen A i).2 ≤ itemBound A r s ∧ (rightItem p chosen A i).2 ≤ itemBound A r s := by
  have hCount : count l ≤ r := by
    rw [← GeneralPaperPreparedPositiveLabels.size_eq chosen]
    exact GeneralPaperPreparedPositiveLabels.size_le chosen
  have hi : i.val + 1 ≤ r + 1 := by omega
  have hRead := Nat.mul_le_mul_right (A + binaryWordWidth (r + 1) + 1) (Nat.mul_le_mul_left 64 hi)
  have hWeight : rationalWordWidth (p.weights.read (chosen.read i)) ≤ 1 + 2 * s := by
    rw [p.weight_correct]
    exact rationalWordWidth_of_height (h _)
  simp only [weightItem, leftItem, rightItem, p.weights.size]
  unfold readWork itemBound
  exact ⟨by omega, by omega, by omega⟩

theorem array_work {α : Type*} {c : ℕ} (size : ℕ) (hSize : size = c) (A C : ℕ)
    (callback : Fin c → α × ℕ) (h : ∀ i, (callback i).2 ≤ C) :
    (GeneralPaperSizedBitArray.run size hSize A callback).2 ≤ c * C + PaperIndexedArrayConstruction.overhead id A c c := by
  rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_work]
  change (∑ i : Fin c, (callback i).2) + PaperIndexedArrayConstruction.overhead id A c c ≤
    c * C + PaperIndexedArrayConstruction.overhead id A c c
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  have hResult := Nat.add_le_add_right hs (PaperIndexedArrayConstruction.overhead id A c c)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using hResult

def makeBound (A r s : ℕ) : ℕ :=
  3 * r * itemBound A r s + 3 * (r + 1) * (6 * A + 10 * binaryWordWidth (r + 1) + 28) + 64 * A + 64

theorem make_work {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (chosen : Selection l) (A : ℕ) (h : ∀ i, RationalHeight (l.weight i) s) :
    (make p chosen A).2 ≤ makeBound A r s := by
  have hC := item_work p chosen A h
  have hW := array_work chosen.size (GeneralPaperPreparedPositiveLabels.size_eq chosen) A (itemBound A r s)
    (weightItem p chosen A) (fun i => (hC i).1)
  have hP := array_work chosen.size (GeneralPaperPreparedPositiveLabels.size_eq chosen) A (itemBound A r s)
    (leftItem p chosen A) (fun i => (hC i).2.1)
  have hQ := array_work chosen.size (GeneralPaperPreparedPositiveLabels.size_eq chosen) A (itemBound A r s)
    (rightItem p chosen A) (fun i => (hC i).2.2)
  have hCount : count l ≤ r := by
    rw [← GeneralPaperPreparedPositiveLabels.size_eq chosen]
    exact GeneralPaperPreparedPositiveLabels.size_le chosen
  have hCost := Nat.mul_le_mul_right (itemBound A r s) hCount
  have hOver := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega)
    A (count l) (count l) le_rfl
  have hWord := binaryWordWidth_mono (Nat.add_le_add_right hCount 1)
  have hOverScale := Nat.mul_le_mul (Nat.add_le_add_right hCount 1)
    (show 6 * A + 10 * 1 * binaryWordWidth (count l + 1) + 28 ≤
      6 * A + 10 * binaryWordWidth (r + 1) + 28 by omega)
  unfold make makeBound
  dsimp only
  nlinarith only [hW, hP, hQ, hCost, hOver, hOverScale]

def bound (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  GeneralPaperPreparedPositiveLabels.bound model A r s + makeBound A r s + 64 * A + 64

theorem work {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (hs : 2 ≤ s) (h : ∀ i, RationalHeight (l.weight i) s) :
    (run p model A).2 ≤ bound model A r s := by
  have hSelect := GeneralPaperPreparedPositiveLabels.work p model A hs h
  have hMake := make_work p (GeneralPaperPreparedPositiveLabels.run p model A).1 A h
  unfold run bound
  dsimp only
  omega

theorem headline (model : RationalCostModel) (A s : ℕ) :
    bound model A 9 s ≤ 1048576 * (model.rat (1 + 2 * s) + A + 1) := by
  have hWord : binaryWordWidth 10 = 4 := by decide
  have hS := model.word_le (1 + 2 * s)
  unfold bound makeBound itemBound GeneralPaperPreparedPositiveLabels.bound
    GeneralPaperPositiveLabelScan.stepBound GeneralPaperEqualRouteConstruction.indicesWork
  rw [hWord]
  nlinarith only [hS]

end Blotto.GeneralPaperPreparedSegmentCompaction
