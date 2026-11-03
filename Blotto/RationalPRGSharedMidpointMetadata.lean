import Blotto.RationalGroupMidpointMetadata
import Blotto.SharedTerminalWindowWork
import Blotto.RationalPRGOutputHeight

/-! The primary one-state source loop delegates midpoint metadata to the
terminal program at the actual handoff position. Both normalized PRG players
provide their own input lattice; no lattice is assumed from the caller. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedMidpointMetadataBitWork {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits
    (fun value pos hpos => (i.terminalData value).midpointMetadataBitWork primitive K outerBits scalarBits R bits pos hpos)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedMidpointMetadataBitWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedMidpointMetadataBitWork primitive K R outerBits scalarBits bits ≤ 9072 * dyadicMidpointMetadataBound c K := by
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hWork := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value pos hpos => (i.terminalData value).midpointMetadataBitWork primitive K outerBits scalarBits R bits pos hpos)
    (9072 * dyadicMidpointMetadataBound c K) 0
    (fun value _ pos hpos => by
      simpa only [Nat.zero_mul, Nat.add_zero] using
        (i.terminalData value).midpointMetadataBitWork_bound primitive c hPrimitive K outerBits scalarBits R bits pos hpos)
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  simpa only [sharedMidpointMetadataBitWork, Nat.zero_mul, Nat.add_zero] using hWork

noncomputable def sharedPaperMidpointMetadataBitWork {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedMidpointMetadataBitWork primitive K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits) (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

theorem sharedPaperMidpointMetadataBitWork_bounds {n : ℕ} (i : RationalPRGInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperMidpointMetadataBitWork primitive K bits ≤ 9072 * dyadicMidpointMetadataBound c K ∧
      i.poorNativeSystem.sharedPaperMidpointMetadataBitWork primitive K bits ≤ 9072 * dyadicMidpointMetadataBound c K :=
  ⟨i.richNativeSystem_on_lattice.sharedMidpointMetadataBitWork_bound primitive c hPrimitive K _ _ _ _,
    i.poorNativeSystem_on_lattice.sharedMidpointMetadataBitWork_bound primitive c hPrimitive K _ _ _ _⟩

end Blotto.RationalPRGInput
