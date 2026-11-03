import Blotto.BinaryPRGHeapRawWork

/-! Accepted raw frames derive the parameters of the physical general-resource
caller. Add its proved polynomial price to the prior complete source ledger;
all rejection paths retain their original prices. This is not a complete
physical interpretation of the remaining terminal backends or host runtime. -/

namespace Blotto.BinaryPRGHeapRawWorkBound
open BinarySeedLookupTree RationalLottoResourceSystem

theorem read_resource_work_bound : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool),
      (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed →
      ∀ (rich : Bool) (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision),
        (BinaryPRGHeapResourceRequest.run (prepare (List.ofFn tables.choice.read))
          parsed.1.2.request rich).2 ≤ C * (frame.length + 1)^d := by
  rcases BinaryPRGHeapResourceRequest.uniform_request_work_bound with ⟨C,d,hRequest⟩
  refine ⟨C * 10000^d,d,?_⟩
  intro frame parsed hRead rich tables
  let store := prepare (List.ofFn tables.choice.read)
  have h := hRequest store parsed.1.2.request rich
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hRead
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame parsed hRead
  have hW := BinaryPRGFrameCostJoin.read_source_width frame parsed hRead
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
  have hSize : parsed.1.1 + parsed.1.2.request.source.originalInputWordWidth +
      store.width + store.cap.value + 1 ≤ 10000 * (frame.length + 1) := by omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact h.trans (hp.trans_eq (by ring))

theorem run_polynomial : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool),
    (BinaryPRGHeapRawWork.run rich frame seed).2 ≤ C * (frame.length + 1)^d := by
  rcases read_resource_work_bound with ⟨C,d,hResource⟩
  let A := 8623936008 + 2^512 + 2^192 + 108550
  refine ⟨A + C,4 + d,?_⟩
  intro rich frame seed
  have hOld := BinaryPRGWordControllerRawWorkBound.run_polynomial rich frame seed
  change (BinaryPRGWordControllerRawWork.run rich frame seed).2 ≤ A * (frame.length + 1)^4 at hOld
  have hFour : (frame.length + 1)^4 ≤ (frame.length + 1)^(4 + d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hD : (frame.length + 1)^d ≤ (frame.length + 1)^(4 + d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hOld' := hOld.trans (Nat.mul_le_mul_left A hFour)
  rw [Nat.add_mul]
  unfold BinaryPRGHeapRawWork.run
  unfold BinaryPRGWordControllerRawWork.run at hOld'
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
            have hCompare := BinaryPRGHeapRawWork.output_work_compare parsed.1.2 rich tables
            dsimp only at hCompare
            have hPrice := (hResource frame parsed hRead rich tables).trans
              (Nat.mul_le_mul_left C hD)
            omega
      · rename_i hNonempty
        simp only [hNonempty,ite_false] at hOld'
        omega

end Blotto.BinaryPRGHeapRawWorkBound
