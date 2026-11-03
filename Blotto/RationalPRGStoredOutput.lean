import Blotto.RationalPRGStoredSampler
import Blotto.BinaryNativeRowEncoder

/-! Fast-profile framing consumes the actual stored PRG row. Widths follow
from the old exact sample equality; callers supply no width certificate.
The encoding price excludes drawing, cached-header preparation and extraction. -/

namespace Blotto.RationalPRGOriginalInput

def storedRichOutput {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  BinaryNativeRowEncoder.stored header (i.storedRichSample K bits)

def storedPoorOutput {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  BinaryNativeRowEncoder.stored header (i.storedPoorSample K bits)

theorem storedRichOutput_data {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    storedRichOutput (BinaryNatFrame.encode n) i K bits = i.richOutputBits K bits := by
  rw [storedRichOutput, BinaryNativeRowEncoder.stored_data, i.storedRichSample_allocation]
  rfl

theorem storedPoorOutput_data {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    storedPoorOutput (BinaryNatFrame.encode n) i K bits = i.poorOutputBits K bits := by
  rw [storedPoorOutput, BinaryNativeRowEncoder.stored_data, i.storedPoorSample_allocation]
  rfl

theorem storedRichOutput_read {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (storedRichOutput (BinaryNatFrame.encode n) i K bits ++ suffix) =
      some (n, List.ofFn (i.richSample K bits), suffix) := by
  rw [i.storedRichOutput_data]
  exact i.richOutput_readback K bits suffix

theorem storedPoorOutput_read {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (storedPoorOutput (BinaryNatFrame.encode n) i K bits ++ suffix) =
      some (n, List.ofFn (i.poorSample K bits), suffix) := by
  rw [i.storedPoorOutput_data]
  exact i.poorOutput_readback K bits suffix

theorem storedSample_widths {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    rationalWordWidth ((i.storedRichSample K bits).allocation j) ≤
      2^77*(i.originalInputWordWidth+K+6) ∧
    rationalWordWidth ((i.storedPoorSample K bits).allocation j) ≤
      2^77*(i.originalInputWordWidth+K+6) := by
  rw [i.storedRichSample_allocation, i.storedPoorSample_allocation]
  exact i.sample_wordWidths_linear K bits j

def storedEncodingBound {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n) (c K : ℕ) : ℕ :=
  let W := 2^77*(i.originalInputWordWidth+K+6)
  3*header.length+n*(1024*(c+1)*(W+1)*(binaryWordWidth (W+2)+1)+3)+4

theorem storedOutput_encoding_cost {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryNativeRowEncoder.frameWork primitive header (i.storedRichSample K bits).data.toList ≤
      storedEncodingBound header i c K ∧
    BinaryNativeRowEncoder.frameWork primitive header (i.storedPoorSample K bits).data.toList ≤
      storedEncodingBound header i c K :=
  ⟨BinaryNativeRowEncoder.stored_work_bound primitive c hPrimitive header _ _
      (fun j => (i.storedSample_widths K bits j).1),
    BinaryNativeRowEncoder.stored_work_bound primitive c hPrimitive header _ _
      (fun j => (i.storedSample_widths K bits j).2)⟩

theorem storedOutput_read_budgets {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryRatListFrame.FullBudgetList i.a (i.storedRichSample K bits).data.toList ∧
      BinaryRatListFrame.FullBudgetList i.b (i.storedPoorSample K bits).data.toList := by
  simp only [BinaryNativeRowEncoder.array_list, i.storedRichSample_allocation,
    i.storedPoorSample_allocation]
  exact i.output_readback_budgets K bits

end Blotto.RationalPRGOriginalInput
