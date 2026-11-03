import Blotto.GeneralPaperEqualRealDispatchContract

/-! Bit-priced dominant-field selection reads only the once-materialized
short length array. Original values are neither rescanned nor rerounded. -/
namespace Blotto.GeneralPaperEqualBitBoundaryScan
set_option autoImplicit false
set_option maxHeartbeats 1800000

def scan {n : ℕ} (model : RationalCostModel) (A : ℕ) (lengths : FixedArrayTable n ℚ) :
    List (Fin n) → Option (Fin n) × ℕ
  | [] => (none, 32 * A + 32)
  | j :: rest =>
    let tested := GeneralPaperExpressionBitExecution.compare model A 1 (lengths.read j)
    let header := 64 * (A + binaryWordWidth (j.val + 1) + 1)
    if tested.1 then (some j, tested.2 + header)
    else let child := scan model A lengths rest; (child.1, tested.2 + header + child.2)

theorem data {n : ℕ} (model : RationalCostModel) (A : ℕ) (lengths : FixedArrayTable n ℚ) (items : List (Fin n)) :
    (scan model A lengths items).1 = (GeneralPaperEqualRealBoundaryScan.scan lengths items).1 := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
    simp only [scan, GeneralPaperExpressionBitExecution.compare, decide_eq_true_eq, GeneralPaperEqualRealBoundaryScan.scan]
    split_ifs <;> simp only [ih]

def stepBound (model : RationalCostModel) (A n P : ℕ) : ℕ :=
  3 * model.rat P + 96 * (A + binaryWordWidth (n + 1) + 1)

theorem compare_work {n : ℕ} (model : RationalCostModel) (A P : ℕ) (lengths : FixedArrayTable n ℚ)
    (hP : 3 ≤ P) (h : ∀ j, rationalWordWidth (lengths.read j) ≤ P) (j : Fin n) :
    (GeneralPaperExpressionBitExecution.compare model A 1 (lengths.read j)).2 +
      64 * (A + binaryWordWidth (j.val + 1) + 1) ≤ stepBound model A n P := by
  have hOne : rationalWordWidth (1 : ℚ) = 3 := by decide
  have hRat := model.monotone (max_le (hOne ▸ hP) (h j))
  rw [hOne] at hRat
  have hValue := h j
  have hWidth := model.word_le P
  have hIndex := binaryWordWidth_mono (show j.val + 1 ≤ n + 1 by omega)
  unfold GeneralPaperExpressionBitExecution.compare stepBound
  dsimp only
  rw [hOne]
  omega

theorem scan_work {n : ℕ} (model : RationalCostModel) (A P : ℕ) (lengths : FixedArrayTable n ℚ)
    (hP : 3 ≤ P) (h : ∀ j, rationalWordWidth (lengths.read j) ≤ P) (items : List (Fin n)) :
    (scan model A lengths items).2 ≤ items.length * stepBound model A n P + 32 * A + 32 := by
  induction items with
  | nil => simp only [scan, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons j rest ih =>
    have hc := compare_work model A P lengths hP h j
    simp only [scan, List.length_cons]
    split_ifs <;> nlinarith only [hc, ih, Nat.zero_le (rest.length * stepBound model A n P)]

def run {n : ℕ} (model : RationalCostModel) (A : ℕ) (lengths : FixedArrayTable n ℚ) : Option (Fin n) × ℕ :=
  let ids := GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size
  let actual := scan model A lengths ids
  (actual.1, actual.2 + GeneralPaperEqualRouteConstruction.indicesWork A lengths.data.size + 64 * A + 64)

theorem run_data {n : ℕ} (model : RationalCostModel) (A : ℕ) (lengths : FixedArrayTable n ℚ) :
    (run model A lengths).1 = (GeneralPaperEqualRealBoundaryScan.run lengths).1 := data model A lengths _

theorem run_work {n : ℕ} (model : RationalCostModel) (A P : ℕ) (lengths : FixedArrayTable n ℚ)
    (hP : 3 ≤ P) (h : ∀ j, rationalWordWidth (lengths.read j) ≤ P) :
    (run model A lengths).2 ≤ n * stepBound model A n P +
      GeneralPaperEqualRouteConstruction.indicesWork A n + 96 * A + 96 := by
  have hs := scan_work model A P lengths hP h (GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size)
  rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange] at hs
  dsimp only [run]
  rw [GeneralPaperEqualRouteConstruction.indices_eq, lengths.size]
  omega

theorem native_width {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    let raw := (GeneralPaperValueRoundingPaperContract.run true model W 128 k values).1
    ∀ j, rationalWordWidth ((GeneralPaperEqualLengthArray.run model A raw.1 raw.2).1.read j) ≤
      1 + 6 * (binaryWordWidth n + k + 11) := by
  dsimp only
  let raw := (GeneralPaperValueRoundingPaperContract.run true model W 128 k values).1
  let s := binaryWordWidth n + k + 11
  have hS : 2 ≤ s := by dsimp [s]; omega
  have hD : binaryWordWidth raw.2 ≤ s := (GeneralPaperEqualNativeSampler.roundDen_word true model W k values v hv).trans (by dsimp [s]; omega)
  have hNatD := DyadicMidpointAssembly.nat_height raw.2 s (by omega)
    ((lt_pow_binaryWordWidth raw.2).trans_le (Nat.pow_le_pow_right (by decide) hD))
  intro j
  have ha : raw.1.read j ≤ raw.2 :=
    (Finset.single_le_sum (s := Finset.univ) (f := fun i => raw.1.read i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_eq
      (GeneralPaperValueRoundingPaperContract.source_sum true model W 128 k values)
  have hNatA := DyadicMidpointAssembly.nat_height (raw.1.read j) s (by omega)
    ((lt_pow_binaryWordWidth _).trans_le (Nat.pow_le_pow_right (by decide) ((binaryWordWidth_mono ha).trans hD)))
  have hTwo : RationalHeight (2 : ℚ) s := (show RationalHeight (2 : ℚ) 2 by norm_num [RationalHeight]).mono hS
  have hWord := rationalWordWidth_of_height (hTwo.mul (hNatA.div hNatD))
  rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
  change rationalWordWidth (2 * ((raw.1.read j : ℚ) / raw.2)) ≤ _
  dsimp only [s] at hWord
  omega

end Blotto.GeneralPaperEqualBitBoundaryScan
