import Blotto.RationalScalarUseWork
import Blotto.RationalPRGSharedMidpointMetadata
import Blotto.FairBitBlockReaderWork

/-! Generic scalar invocation prices transfer through the actual shared
source handoff. Unit prices bound call multiplicity; shifted-block read prices
bound each complete outer/scalar block invocation without assuming caching. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedScalarUseWork {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (outerPrice scalarPrice : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits
    (fun value pos hpos => (i.terminalData value).scalarUseWork K outerBits scalarBits outerPrice scalarPrice R bits pos hpos)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedScalarUseWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ} (h : i.OnLattice D)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (outerPrice scalarPrice bound : ℕ)
    (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound) (bits : Fin R → Bool) :
    i.sharedScalarUseWork K R outerBits scalarBits outerPrice scalarPrice bits ≤ 9072 * bound := by
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hWork := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value pos hpos => (i.terminalData value).scalarUseWork K outerBits scalarBits outerPrice scalarPrice R bits pos hpos)
    (9072 * bound) 0
    (fun value _ pos hpos => by
      simpa only [Nat.zero_mul, Nat.add_zero] using
        (i.terminalData value).scalarUseWork_bound K outerBits scalarBits outerPrice scalarPrice bound hOuter hScalar R bits pos hpos)
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  simpa only [sharedScalarUseWork, Nat.zero_mul, Nat.add_zero] using hWork

noncomputable def sharedPaperScalarUseWork {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerPrice scalarPrice : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedScalarUseWork K (coinBitBudget n K) (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner) outerPrice scalarPrice (firstBitBlock (coinBitBudget n K) K inner)

noncomputable def sharedPaperScalarReaderWork {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  i.sharedPaperScalarUseWork K (shiftedBitBlockReaderWork primitive (innerBitBudget n K) K)
    (shiftedBitBlockReaderWork primitive (coinBitBudget n K) K) bits

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

theorem sharedPaperScalarUseWork_bounds {n : ℕ} (i : RationalPRGInput n) (K : ℕ) (outerPrice scalarPrice bound : ℕ)
    (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperScalarUseWork K outerPrice scalarPrice bits ≤ 9072 * bound ∧
      i.poorNativeSystem.sharedPaperScalarUseWork K outerPrice scalarPrice bits ≤ 9072 * bound :=
  ⟨i.richNativeSystem_on_lattice.sharedScalarUseWork_bound K _ _ _ outerPrice scalarPrice bound hOuter hScalar _,
    i.poorNativeSystem_on_lattice.sharedScalarUseWork_bound K _ _ _ outerPrice scalarPrice bound hOuter hScalar _⟩

theorem sharedPaperScalarUseCount_bounds {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperScalarUseWork K 1 1 bits ≤ 9072 ∧
      i.poorNativeSystem.sharedPaperScalarUseWork K 1 1 bits ≤ 9072 := by
  simpa only [Nat.mul_one] using i.sharedPaperScalarUseWork_bounds K 1 1 1 le_rfl le_rfl bits

def scalarReaderUnitBound (c total : ℕ) : ℕ := (5 + c) * binaryWordWidth (total + 1) + 1

theorem scalarReaderUnitBound_mono (c : ℕ) : Monotone (scalarReaderUnitBound c) := by
  intro a b hab
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (binaryWordWidth_mono (Nat.add_le_add_right hab 1))) 1

theorem sharedPaperScalarReaderWork_bounds {n : ℕ} (i : RationalPRGInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperScalarReaderWork primitive K bits ≤ 9072 * (K * scalarReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K)) ∧
      i.poorNativeSystem.sharedPaperScalarReaderWork primitive K bits ≤ 9072 * (K * scalarReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K)) := by
  have hOuter := shiftedBitBlockReaderWork_bound primitive c hPrimitive (RationalLottoResourceSystem.innerBitBudget n K) K
  have hScalar := shiftedBitBlockReaderWork_bound primitive c hPrimitive (RationalLottoResourceSystem.coinBitBudget n K) K
  have hWidth := binaryWordWidth_mono (show RationalLottoResourceSystem.coinBitBudget n K + K + 1 ≤
      RationalLottoResourceSystem.sampleBitBudget n K + 1 by
        unfold RationalLottoResourceSystem.sampleBitBudget RationalLottoResourceSystem.innerBitBudget
        omega)
  have hScalarPrice := hScalar.trans (Nat.mul_le_mul_left K
    (Nat.add_le_add_right (Nat.mul_le_mul_left (5 + c) hWidth) 1))
  exact i.sharedPaperScalarUseWork_bounds K _ _ _ hOuter hScalarPrice bits

end Blotto.RationalPRGInput
