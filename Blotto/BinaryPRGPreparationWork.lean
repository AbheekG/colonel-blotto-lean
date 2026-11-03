import Blotto.BinaryPRGPreparation

/-! Instrumented native numerical preparation uses actual returned Boolean
arithmetic results. Its work is bounded by the stored original input width,
without a supplied operand-width or arithmetic-price oracle. This prices the
arithmetic calls and derived output payload; table/address/control allocation,
promise checking, parsing and full sampler/physical-space costs are separate. -/

namespace Blotto.BinaryPRGPreparationWork
open BinaryRationalNormalization BinaryRationalOpcode BinaryPRGRecognition BinaryPRGPreparation
open scoped BigOperators

theorem canonicalize_stored_width (word : SignedWord) : width (canonicalize word) ≤ width word := by
  have hn := BinaryCanonicalMagnitude.trim_length (normalize word).numerator
  have hd := BinaryCanonicalMagnitude.trim_length (normalize word).denominator
  rw [(normalize_lengths word).1] at hn
  rw [(normalize_lengths word).2] at hd
  exact max_le (hn.trans (Nat.le_max_left _ _)) (hd.trans (Nat.le_max_right _ _))

theorem apply_stored_width (op : RealArithmeticOp) (first second : SignedWord) :
    width (apply op first second) ≤ 3 * BinaryRationalArithmetic.pairWidth first second + 1 :=
  (canonicalize_stored_width _).trans (rawApply_width op first second)

def storedInputWidth {n : ℕ} (input : BinaryPRGRecognition.Input n) : ℕ :=
  width input.a + width input.b + (∑ j, width (input.values.read j)) + 2

theorem original_widths {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    width input.a ≤ storedInputWidth input ∧ width input.b ≤ storedInputWidth input ∧
      (∀ j, width (input.values.read j) ≤ storedInputWidth input) ∧ 2 ≤ storedInputWidth input := by
  refine ⟨by unfold storedInputWidth; omega, by unfold storedInputWidth; omega, ?_, by unfold storedInputWidth; omega⟩
  intro j
  have hs : width (input.values.read j) ≤ ∑ k, width (input.values.read k) :=
    Finset.single_le_sum (f := fun k : Fin n => width (input.values.read k))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold storedInputWidth
  omega

def prepareWithWork {n : ℕ} (input : BinaryPRGRecognition.Input n) : Prepared n × ℕ :=
  let ratio := applyWithWork .div input.b input.a
  let lengths := FixedArrayTable.ofFn (fun j => applyWithWork .mul two (input.values.read j))
  let poor := FixedArrayTable.ofFn (fun j => applyWithWork .mul ratio.1 (lengths.read j).1)
  (⟨input, ratio.1, FixedArrayTable.ofFn (fun j => (lengths.read j).1),
      FixedArrayTable.ofFn (fun j => (poor.read j).1)⟩,
    ratio.2 + (∑ j, (lengths.read j).2) + ∑ j, (poor.read j).2)

theorem prepareWithWork_refines {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    (prepareWithWork input).1 = prepare input := by
  simp only [prepareWithWork, prepare, FixedArrayTable.read_ofFn, applyWithWork_state]

theorem prepareWithWork_work {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    (prepareWithWork input).2 = (applyWithWork .div input.b input.a).2 +
      (∑ j, (applyWithWork .mul two (input.values.read j)).2) +
      ∑ j, (applyWithWork .mul (apply .div input.b input.a)
        (apply .mul two (input.values.read j))).2 := by
  simp only [prepareWithWork, FixedArrayTable.read_ofFn, applyWithWork_state]

theorem ratio_width {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    width (prepare input).ratio ≤ 3 * storedInputWidth input + 1 := by
  have h := original_widths input
  exact (apply_stored_width .div input.b input.a).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le h.2.1 h.1)) 1)

theorem lengths_width {n : ℕ} (input : BinaryPRGRecognition.Input n) (j : Fin n) :
    width ((prepare input).lengths.read j) ≤ 3 * storedInputWidth input + 1 := by
  have h := original_widths input
  have hTwo : width two = 2 := rfl
  change width ((FixedArrayTable.ofFn _).read j) ≤ _
  rw [FixedArrayTable.read_ofFn]
  exact (apply_stored_width .mul two _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le (by rw [hTwo]; exact h.2.2.2) (h.2.2.1 j))) 1)

theorem poorResources_width {n : ℕ} (input : BinaryPRGRecognition.Input n) (j : Fin n) :
    width ((prepare input).poorResources.read j) ≤ 9 * storedInputWidth input + 4 := by
  change width ((FixedArrayTable.ofFn _).read j) ≤ _
  rw [FixedArrayTable.read_ofFn]
  change width (apply .mul (prepare input).ratio ((prepare input).lengths.read j)) ≤ _
  have h := (apply_stored_width .mul _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le (ratio_width input) (lengths_width input j))) 1)
  exact h.trans_eq (by ring)

theorem operation_uniform_bound (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hA : width first ≤ W) (hB : width second ≤ W) :
    (applyWithWork op first second).2 ≤ 12000 * (W + 1) ^ 3 :=
  (applyWithWork_bound op first second).trans
    (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hA hB) 1) 3))

set_option maxHeartbeats 1000000 in
theorem prepareWithWork_bound {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    (prepareWithWork input).2 ≤ (1 + 2 * n) * (12000 * (3 * storedInputWidth input + 2) ^ 3) := by
  let W := 3 * storedInputWidth input + 1
  let P := 12000 * (W + 1) ^ 3
  have h := original_widths input
  have hA : width input.a ≤ W := by dsimp [W]; omega
  have hB : width input.b ≤ W := by dsimp [W]; omega
  have hTwo : width two ≤ W := by change 2 ≤ W; dsimp [W]; omega
  have hValue : ∀ j, width (input.values.read j) ≤ W := by intro j; have hv := h.2.2.1 j; dsimp [W]; omega
  have hRatio := operation_uniform_bound .div input.b input.a W hB hA
  have hLengths : ∑ j, (applyWithWork .mul two (input.values.read j)).2 ≤ n * P := by
    calc
      _ ≤ ∑ _j : Fin n, P := Finset.sum_le_sum (fun j _ => operation_uniform_bound .mul _ _ W hTwo (hValue j))
      _ = _ := by simp
  have hPoor : ∑ j,
      (applyWithWork .mul (prepare input).ratio ((prepare input).lengths.read j)).2 ≤ n * P := by
    calc
      _ ≤ ∑ _j : Fin n, P := Finset.sum_le_sum (fun j _ => operation_uniform_bound .mul _ _ W (ratio_width input) (lengths_width input j))
      _ = _ := by simp
  simp only [prepare, FixedArrayTable.read_ofFn] at hPoor
  rw [prepareWithWork_work]
  have hTotal := Nat.add_le_add (Nat.add_le_add hRatio hLengths) hPoor
  apply hTotal.trans_eq
  dsimp [P, W]
  ring

def preparedPayload {n : ℕ} (prepared : Prepared n) : ℕ :=
  BinaryRationalRegisterProgram.payloadWords prepared.ratio +
    (∑ j, BinaryRationalRegisterProgram.payloadWords (prepared.lengths.read j)) +
    ∑ j, BinaryRationalRegisterProgram.payloadWords (prepared.poorResources.read j)

theorem preparedPayload_bound {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    preparedPayload (prepare input) ≤ (1 + 2 * n) * (18 * storedInputWidth input + 9) := by
  let W := 9 * storedInputWidth input + 4
  have hRatio : width (prepare input).ratio ≤ W := (ratio_width input).trans (by dsimp [W]; omega)
  have hLengths : ∀ j, width ((prepare input).lengths.read j) ≤ W :=
    fun j => (lengths_width input j).trans (by dsimp [W]; omega)
  have hPoor : ∀ j, width ((prepare input).poorResources.read j) ≤ W := poorResources_width input
  have hR := BinaryRationalRegisterProgram.payloadWords_bound _ W hRatio
  have hL : ∑ j, BinaryRationalRegisterProgram.payloadWords ((prepare input).lengths.read j) ≤ n * (1 + 2 * W) := by
    calc
      _ ≤ ∑ _j : Fin n, (1 + 2 * W) := Finset.sum_le_sum (fun j _ => BinaryRationalRegisterProgram.payloadWords_bound _ W (hLengths j))
      _ = _ := by simp
  have hP : ∑ j, BinaryRationalRegisterProgram.payloadWords ((prepare input).poorResources.read j) ≤ n * (1 + 2 * W) := by
    calc
      _ ≤ ∑ _j : Fin n, (1 + 2 * W) := Finset.sum_le_sum (fun j _ => BinaryRationalRegisterProgram.payloadWords_bound _ W (hPoor j))
      _ = _ := by simp
  unfold preparedPayload
  dsimp [W] at hR hL hP
  nlinarith

end Blotto.BinaryPRGPreparationWork
