import Blotto.BinaryFrameEncodingMetadata
import Blotto.RationalArrayConstructionWork
import Blotto.RationalPRGOutputEncodingCost

/-! Both original-budget output paths add scaled-row construction and frame
iterator/buffer metadata. Every array push may copy its old prefix. These
prices cover all bit/fallback paths and remain separate from local producer
metadata and physical addresses/backend/ownership/space. -/

namespace Blotto.RationalPRGOriginalInput
open scoped BigOperators

def outputMetadataWidth {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  2 ^ 77 * (i.originalInputWordWidth + K + 6)

def richOutputMetadataBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  rationalArrayCopyWork (List.ofFn (i.richSample K bits)) 0 + indexedLoopMetadataBitWork primitive 0 n +
    BinaryRatListFrame.rowEncodingMetadataBitWork primitive (i.richSample K bits)

def poorOutputMetadataBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  rationalArrayCopyWork (List.ofFn (i.poorSample K bits)) 0 + indexedLoopMetadataBitWork primitive 0 n +
    BinaryRatListFrame.rowEncodingMetadataBitWork primitive (i.poorSample K bits)

def outputMetadataBound (c n W : ℕ) : ℕ :=
  2 * n * (n * W) + indexedLoopMetadataBound c n + BinaryRatListFrame.rowEncodingMetadataBound c n W

theorem outputMetadataBound_mono (c : ℕ) {n N W V : ℕ} (hn : n ≤ N) (hW : W ≤ V) :
    outputMetadataBound c n W ≤ outputMetadataBound c N V := by
  have hLoop := indexedLoopMetadataBound_mono c hn
  have hFrame := BinaryRatListFrame.rowEncodingMetadataBound_mono c hn hW
  unfold outputMetadataBound
  gcongr

theorem outputMetadataBitWork_bounds {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richOutputMetadataBitWork primitive K bits ≤ outputMetadataBound c n (i.outputMetadataWidth K) ∧
      i.poorOutputMetadataBitWork primitive K bits ≤ outputMetadataBound c n (i.outputMetadataWidth K) := by
  have hRows : ∀ row : Fin n → ℚ, (∀ j, rationalWordWidth (row j) ≤ i.outputMetadataWidth K) →
      rationalArrayCopyWork (List.ofFn row) 0 + indexedLoopMetadataBitWork primitive 0 n +
        BinaryRatListFrame.rowEncodingMetadataBitWork primitive row ≤ outputMetadataBound c n (i.outputMetadataWidth K) := by
    intro row hRow
    have hCopy := rationalArrayCopyWork_bound (List.ofFn row) 0
    have hWords := rationalWordWidth_sum_bound (List.ofFn row) (i.outputMetadataWidth K)
      (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact hRow j)
    simp only [List.length_ofFn, Nat.zero_add] at hCopy hWords
    have hCopyPrice := hCopy.trans (Nat.mul_le_mul_left (2 * n) hWords)
    have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive n
    have hFrame := BinaryRatListFrame.rowEncodingMetadataBitWork_bound primitive c hPrimitive row _ hRow
    unfold outputMetadataBound
    omega
  exact ⟨hRows (i.richSample K bits) (fun j => (i.sample_wordWidths_linear K bits j).1),
    hRows (i.poorSample K bits) (fun j => (i.sample_wordWidths_linear K bits j).2)⟩

def selectedOutputMetadataBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.richOutputMetadataBitWork primitive K bits else i.poorOutputMetadataBitWork primitive K bits

theorem selectedOutputMetadataBitWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedOutputMetadataBitWork primitive rich K bits ≤ outputMetadataBound c n (i.outputMetadataWidth K) := by
  have h := i.outputMetadataBitWork_bounds primitive c hPrimitive K bits
  cases rich with
  | false => exact h.2
  | true => exact h.1

end Blotto.RationalPRGOriginalInput
