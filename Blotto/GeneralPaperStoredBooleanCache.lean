import Blotto.GeneralPaperStoredWordEncoding

/-! Materialize Boolean categorical data from stored width/counts. Runtime
labels use the count array's retained size; each word is encoded once. -/
namespace Blotto.GeneralPaperStoredBooleanCache
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def rows {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width : ℕ) :
    List (Fin c) → List (Fin c × FixedBinaryWord width) × ℕ
  | [] => ([], 32 * A + 32)
  | i :: rest =>
    let encoded := GeneralPaperStoredWordEncoding.word model A width (counts.read i)
    let child := rows counts model A width rest
    ((i, encoded.1) :: child.1, encoded.2 + child.2 + 64 * (A + binaryWordWidth (i.val + 1) + 1))

theorem rows_data {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width : ℕ)
    (items : List (Fin c)) :
    (rows counts model A width items).1 = items.map (fun i => (i, FixedBinaryWord.ofNat width (counts.read i))) := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
    rw [rows]
    dsimp only
    rw [GeneralPaperStoredWordEncoding.word_data, ih]
    rfl

def run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) : GeneralPaperEqualBooleanCache.Cache p × ℕ :=
  let width := p.rangeBits + 1
  let denominator := GeneralPaperStoredWordEncoding.word model A width p.D
  let labels := GeneralPaperEqualRouteConstruction.indices p.counts.data.size p.counts.size
  let words := rows p.counts model A width labels
  let actual : GeneralPaperEqualBooleanCache.Cache p :=
    ⟨denominator.1, (by
      rw [GeneralPaperStoredWordEncoding.word_data]
      exact FixedBinaryWord.value_ofNat _ _ (GeneralPaperEqualBooleanCache.denominator_fits p)),
      words.1, (by
        dsimp only [words, labels]
        rw [rows_data, GeneralPaperEqualRouteConstruction.indices_eq, ← List.ofFn_eq_map]
        rfl), List.replicate p.rangeBits (), (by simp)⟩
  (actual, denominator.2 + words.2 + GeneralPaperEqualRouteConstruction.indicesWork A p.counts.data.size +
    64 * (p.rangeBits + 1) * (A + binaryWordWidth (p.rangeBits + 1) + 1) + 128 * A + 128)

theorem data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) :
    (run p model A).1 = GeneralPaperEqualBooleanCache.prepare p := by
  simp only [run, GeneralPaperStoredWordEncoding.word_data, rows_data,
    GeneralPaperEqualRouteConstruction.indices_eq, ← List.ofFn_eq_map,
    GeneralPaperEqualBooleanCache.prepare, GeneralPaperEqualBooleanCache.word]

def rowBound (model : RationalCostModel) (A c width L : ℕ) : ℕ :=
  width * GeneralPaperStoredWordEncoding.stepBound model A width L + 64 * A + 64 +
    64 * (A + binaryWordWidth (c + 1) + 1)

theorem rows_work {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width L : ℕ)
    (h : ∀ i, binaryWordWidth (counts.read i) ≤ L) (items : List (Fin c)) :
    (rows counts model A width items).2 ≤ items.length * rowBound model A c width L + 32 * A + 32 := by
  induction items with
  | nil => simp only [rows, List.length_nil, zero_mul, zero_add, le_refl]
  | cons i rest ih =>
    have hWord := GeneralPaperStoredWordEncoding.work model A width (counts.read i) L (h i)
    have hIndex := binaryWordWidth_mono (show i.val + 1 ≤ c + 1 by omega)
    rw [rows]
    dsimp only
    simp only [List.length_cons]
    unfold rowBound at ih ⊢
    nlinarith only [ih, hWord, hIndex]

def bound (model : RationalCostModel) (A c width L : ℕ) : ℕ :=
  (width + 1) * GeneralPaperStoredWordEncoding.stepBound model A (width + 1) L + 64 * A + 64 +
    c * rowBound model A c (width + 1) L + 32 * A + 32 +
    GeneralPaperEqualRouteConstruction.indicesWork A c +
    64 * (width + 1) * (A + binaryWordWidth (width + 1) + 1) + 128 * A + 128

theorem work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (model : RationalCostModel) (A L : ℕ) (hD : binaryWordWidth p.D ≤ L) :
    (run p model A).2 ≤ bound model A (count l) p.rangeBits L := by
  have hDen := GeneralPaperStoredWordEncoding.work model A (p.rangeBits + 1) p.D L hD
  have hCounts : ∀ i, binaryWordWidth (p.counts.read i) ≤ L := fun i =>
    (binaryWordWidth_mono (GeneralPaperEqualPreparedCache.counts_bounded p i)).trans hD
  have hRows := rows_work p.counts model A (p.rangeBits + 1) L hCounts
    (GeneralPaperEqualRouteConstruction.indices p.counts.data.size p.counts.size)
  rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange] at hRows
  unfold run bound
  dsimp only
  rw [GeneralPaperEqualRouteConstruction.indices_eq, p.counts.size]
  omega

theorem headline (model : RationalCostModel) (A c width L : ℕ) (hc : c ≤ 7) (hw : width ≤ L) :
    bound model A c width L ≤ 8192 * (L + 1) * (model.rat (L + 8) + A + 1) := by
  let P := model.rat (L + 8) + A + 1
  have hP : A + L + 9 ≤ P := by
    have h := model.word_le (L + 8)
    dsimp only [P]
    omega
  have hRat := model.monotone (show L + 4 ≤ L + 8 by omega)
  have hW : binaryWordWidth (width + 2) ≤ L + 3 := by
    have h := Nat.log2_le_self (width + 2)
    unfold binaryWordWidth
    omega
  have hW' : binaryWordWidth (width + 1) ≤ L + 2 := by
    have h := Nat.log2_le_self (width + 1)
    unfold binaryWordWidth
    omega
  have hC : binaryWordWidth (c + 1) ≤ 4 := by
    have h := binaryWordWidth_mono (show c + 1 ≤ 8 by omega)
    have h8 : binaryWordWidth 8 = 4 := by decide
    omega
  have hStep : GeneralPaperStoredWordEncoding.stepBound model A (width + 1) L ≤ 136 * P := by
    unfold GeneralPaperStoredWordEncoding.stepBound
    have hEq : width + 1 + 1 = width + 2 := by omega
    rw [hEq]
    dsimp only [P] at hP ⊢
    omega
  have hDen := Nat.mul_le_mul (show width + 1 ≤ L + 1 by omega) hStep
  have hRow : rowBound model A c (width + 1) L ≤ 512 * (L + 1) * P := by
    unfold rowBound
    nlinarith only [hDen, hP, hC]
  have hRows := Nat.mul_le_mul hc hRow
  have hIndices : GeneralPaperEqualRouteConstruction.indicesWork A c ≤ 512 * P := by
    have h := Nat.mul_le_mul (show c + 1 ≤ 8 by omega)
      (show A + binaryWordWidth (c + 1) + 1 ≤ P by omega)
    unfold GeneralPaperEqualRouteConstruction.indicesWork
    nlinarith only [h]
  have hRuler := Nat.mul_le_mul (show width + 1 ≤ L + 1 by omega)
    (show A + binaryWordWidth (width + 1) + 1 ≤ P by omega)
  unfold bound
  change _ ≤ 8192 * (L + 1) * P
  nlinarith only [hDen, hP, hRows, hIndices, hRuler]

end Blotto.GeneralPaperStoredBooleanCache
