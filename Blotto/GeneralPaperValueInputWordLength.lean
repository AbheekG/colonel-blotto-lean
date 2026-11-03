import Blotto.GeneralPaperEqualResourceDomain

/-! A single pass measures the aggregate original rational input words.
Only the short returned lengths are added; every original word scan is
charged additively. This is input inspection, not a heap or cost census. -/
namespace Blotto.GeneralPaperValueInputWordLength
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def size {n : ℕ} (values : FixedArrayTable n ℚ) (items : List (Fin n)) : ℕ :=
  (items.map (fun j => rationalWordWidth (values.read j))).sum

def scan {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) : List (Fin n) → ℕ × ℕ
  | [] => (0, 64 * A + 64)
  | j :: rest =>
    let measured := GeneralPaperStoredRationalWordLength.run model A (values.read j)
    let later := scan model A values rest
    let joined := GeneralPaperNaturalScalarStep.run model A .add measured.1 later.1
    (joined.1, measured.2 + later.2 + joined.2 + GeneralPaperEqualPackingExecution.unit A n + 64 * A + 64)

theorem scan_data {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (items : List (Fin n)) :
    (scan model A values items).1 = size values items := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
    simp only [scan, GeneralPaperNaturalScalarStep.data, GeneralPaperNaturalScalarStep.Op.apply,
      GeneralPaperStoredRationalWordLength.data, ih, size, List.map_cons, List.sum_cons]

def unit (model : RationalCostModel) (A n S : ℕ) : ℕ :=
  4096 * (A + binaryWordWidth (n + 1) + model.rat (8 * (binaryWordWidth (S + 1) + 1)) + 1)

theorem scan_work {n : ℕ} (model : RationalCostModel) (A S : ℕ) (values : FixedArrayTable n ℚ)
    (items : List (Fin n)) (hSize : size values items ≤ S) :
    (scan model A values items).2 ≤ 1024 * size values items + items.length * unit model A n S + 64 * A + 64 := by
  induction items with
  | nil => simp only [scan, size, List.map_nil, List.sum_nil, List.length_nil, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons j rest ih =>
    have hSize' : rationalWordWidth (values.read j) + size values rest ≤ S := hSize
    have hRest := ih (by omega)
    have hWord := GeneralPaperStoredRationalWordLength.work model A (values.read j)
    have hWidth : binaryWordWidth (rationalWordWidth (values.read j)) ≤ binaryWordWidth (S + 1) :=
      binaryWordWidth_mono (by omega)
    have hRat := model.monotone (show binaryWordWidth (rationalWordWidth (values.read j)) + 3 ≤
      8 * (binaryWordWidth (S + 1) + 1) by omega)
    have ha : GeneralPaperNaturalScalarStep.word (rationalWordWidth (values.read j)) ≤
        8 * (binaryWordWidth (S + 1) + 1) := by unfold GeneralPaperNaturalScalarStep.word; omega
    have hb : GeneralPaperNaturalScalarStep.word (size values rest) ≤
        8 * (binaryWordWidth (S + 1) + 1) := by
      have h := binaryWordWidth_mono (show size values rest ≤ S + 1 by omega)
      unfold GeneralPaperNaturalScalarStep.word
      omega
    have ho : GeneralPaperNaturalScalarStep.word (rationalWordWidth (values.read j) + size values rest) ≤
        8 * (binaryWordWidth (S + 1) + 1) := by
      have h := binaryWordWidth_mono (show rationalWordWidth (values.read j) + size values rest ≤ S + 1 by omega)
      unfold GeneralPaperNaturalScalarStep.word
      omega
    have hJoin := GeneralPaperNaturalScalarStep.work model A .add (rationalWordWidth (values.read j))
      (size values rest) (8 * (binaryWordWidth (S + 1) + 1)) ha hb ho
    simp only [scan, GeneralPaperStoredRationalWordLength.data, scan_data]
    change (GeneralPaperStoredRationalWordLength.run model A (values.read j)).2 +
      (scan model A values rest).2 +
      (GeneralPaperNaturalScalarStep.run model A .add (rationalWordWidth (values.read j)) (size values rest)).2 +
      GeneralPaperEqualPackingExecution.unit A n + 64 * A + 64 ≤ _
    change _ ≤ 1024 * (rationalWordWidth (values.read j) + size values rest) +
      (rest.length + 1) * unit model A n S + 64 * A + 64
    unfold unit GeneralPaperEqualPackingExecution.unit at *
    nlinarith only [hWord, hRat, hRest, hJoin]

def run {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) : ℕ × ℕ :=
  let indices := List.finRange n
  let measured := scan model A values indices
  (measured.1, measured.2 + GeneralPaperEqualRouteConstruction.indicesWork A n + 64 * A + 64)

theorem full_size {n : ℕ} (values : FixedArrayTable n ℚ) :
    size values (List.finRange n) = GeneralPaperValueRoundingInputPrice.inputSize values := by
  simp only [size, ← List.ofFn_eq_map, List.sum_ofFn, GeneralPaperValueRoundingInputPrice.inputSize]

theorem data {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) :
    (run model A values).1 = GeneralPaperValueRoundingInputPrice.inputSize values := by
  simp only [run, scan_data, full_size]

def profile (model : RationalCostModel) (A n S : ℕ) : ℕ :=
  1024 * S + n * unit model A n S + GeneralPaperEqualRouteConstruction.indicesWork A n + 128 * A + 128

theorem work {n : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) :
    (run model A values).2 ≤ profile model A n (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  have h := scan_work model A (GeneralPaperValueRoundingInputPrice.inputSize values) values (List.finRange n) (full_size values).le
  simp only [full_size, List.length_finRange] at h
  unfold run profile
  dsimp only
  omega

end Blotto.GeneralPaperValueInputWordLength
