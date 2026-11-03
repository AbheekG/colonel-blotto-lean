import Blotto.BinaryPRGHeapCompleteRawWork

/-! Accepted frames derive the reflected source height and seed parameters.
Together with the physical general-resource bound this gives a uniform
polynomial bound on the complete recorded ledger, including rejection paths. -/

namespace Blotto.BinaryPRGHeapCompleteRawWorkBound
open BinarySeedLookupTree RationalLottoResourceSystem

theorem read_reflected_bound : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool),
      (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed →
      ∀ (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision),
        let store := prepare (List.ofFn tables.choice.read)
        BinaryPRGHeapReflectedSetup.bound (BinaryCachedTerminalPrimitiveRun.requestHeight parsed.1.2.request)
          store.width store.cap.value ≤ C * (frame.length + 1)^d := by
  rcases BinaryPRGHeapReflectedSetup.bound_polynomial with ⟨C,d,hBound⟩
  refine ⟨C * 10000^d,d,?_⟩
  intro frame parsed hRead tables
  let store := prepare (List.ofFn tables.choice.read)
  have h := hBound ⟨0,BinaryCachedTerminalPrimitiveRun.requestHeight parsed.1.2.request,0,
    store.width,store.cap.value⟩
  simp only [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth,Nat.log2_zero,Nat.zero_add] at h
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hRead
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame parsed hRead
  have hW := BinaryPRGFrameCostJoin.read_source_width frame parsed hRead
  have hInput : BinaryCachedGroupInputHeight.inputHeight parsed.1.2.request ≤ 32 * (frame.length + 1) := by
    unfold BinaryCachedGroupInputHeight.inputHeight
    omega
  have hRequest : BinaryCachedTerminalPrimitiveRun.requestHeight parsed.1.2.request ≤ 32 * (frame.length + 1) := by
    unfold BinaryCachedTerminalPrimitiveRun.requestHeight
    exact max_le hInput (by omega)
  have hCap : store.cap.value = coinBitBudget parsed.1.1 parsed.1.2.request.precision := by
    dsimp only [store]
    rw [cap_value,List.length_ofFn]
  have hN : store.cap.value ≤ 3015 * (frame.length + 1) := by
    rw [hCap]
    unfold coinBitBudget
    omega
  have hWidth := prepare_width_bound (List.ofFn tables.choice.read)
  simp only [List.length_ofFn] at hWidth
  have hIndex : store.width ≤ 3016 * (frame.length + 1) := by
    have hLog := Nat.log2_le_self (coinBitBudget parsed.1.1 parsed.1.2.request.precision)
    unfold binaryWordWidth at hWidth
    change store.width ≤ _ at hWidth
    rw [hCap] at hN
    omega
  have hSize : BinaryCachedTerminalPrimitiveRun.requestHeight parsed.1.2.request + 1 +
      store.width + store.cap.value + 1 ≤ 10000 * (frame.length + 1) := by omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact h.trans (hp.trans_eq (by ring))

theorem run_polynomial : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    (BinaryPRGHeapCompleteRawWork.run rich frame seed).2 ≤ C * (frame.length + 1)^d := by
  rcases read_reflected_bound with ⟨C,d,hReflected⟩
  rcases BinaryPRGHeapRawWorkBound.run_polynomial with ⟨A,e,hOld⟩
  refine ⟨A + C,e + d,?_⟩
  intro rich frame seed
  have hE : (frame.length + 1)^e ≤ (frame.length + 1)^(e + d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hD : (frame.length + 1)^d ≤ (frame.length + 1)^(e + d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hOld' := (hOld rich frame seed).trans (Nat.mul_le_mul_left A hE)
  rw [Nat.add_mul]
  unfold BinaryPRGHeapCompleteRawWork.run
  unfold BinaryPRGHeapRawWork.run at hOld'
  dsimp only at hOld' ⊢
  cases hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 with
  | none =>
      simp only [hRead] at hOld' ⊢
      omega
  | some parsed =>
      simp only [hRead] at hOld' ⊢
      split
      · rename_i hEmpty
        simp only [hEmpty,ite_true] at hOld'
        cases hSeed : (BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed).1 with
        | none =>
            simp only [hSeed] at hOld' ⊢
            omega
        | some tables =>
            simp only [hSeed] at hOld' ⊢
            have hCompare := BinaryPRGHeapCompleteRawWork.output_cost_le parsed.1.2 rich tables
            dsimp only at hCompare
            have hPrice := (hReflected frame parsed hRead tables).trans (Nat.mul_le_mul_left C hD)
            omega
      · rename_i hNonempty
        simp only [hNonempty,ite_false] at hOld'
        omega

end Blotto.BinaryPRGHeapCompleteRawWorkBound
