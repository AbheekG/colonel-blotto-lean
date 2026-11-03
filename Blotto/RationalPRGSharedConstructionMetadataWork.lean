import Blotto.RationalGroupConstructionMetadataWork
import Blotto.SharedTerminalWindowWork
import Blotto.RationalPRGOutputHeight

/-! Runtime factory metadata transfers through the primary shared source
handoff. Both normalized player systems supply their actual input lattice. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedConstructionMetadataWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (c K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits
    (fun value pos hpos => (i.terminalData value).runtimeConstructionMetadataWork primitive c K outerBits scalarBits R bits pos hpos)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)


theorem OnLattice.sharedConstructionMetadataWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedConstructionMetadataWork primitive c K R outerBits scalarBits bits ≤
      2592 * RationalTerminalResources.profileConstructionMetadataBound c
        (expressionHeightBudget (max s (K + 2)) 22) K := by
  let A := 2592 * RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget (max s (K + 2)) 22) K
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value pos hpos => (i.terminalData value).runtimeConstructionMetadataWork primitive c K outerBits scalarBits R bits pos hpos)
    A 0
    (fun value hValue pos hpos => by
      exact ((h.terminalData value hValue).runtimeConstructionMetadataWork_bound hD hB s hs hBudget hWidth primitive c hPrimitive
        K outerBits scalarBits R bits pos hpos).trans (Nat.le_add_right _ _))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  have he : A + 0 * (R - 0) = A :=
    (congrArg (fun t : ℕ => A + t) (Nat.zero_mul (R - 0))).trans (Nat.add_zero A)
  exact hp.trans_eq he


noncomputable def sharedPaperConstructionMetadataWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (c K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedConstructionMetadataWork primitive c K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits) (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)


end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedConstructionMetadataWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.sharedPaperConstructionMetadataWork primitive c K bits
  else i.normalizedInput.poorNativeSystem.sharedPaperConstructionMetadataWork primitive c K bits


theorem selectedConstructionMetadataWork_bound {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedConstructionMetadataWork primitive c rich K bits ≤
      2592 * RationalTerminalResources.profileConstructionMetadataBound c
        (expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 22) K := by
  have hs : 2 ≤ 3 + i.originalInputWordWidth := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ 3 + i.originalInputWordWidth :=
    i.normalized_lattice_wordWidth_original.trans (by omega)
  have hOne : RationalHeight (1 : ℚ) (3 + i.originalInputWordWidth) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.sharedConstructionMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le _ hs i.normalized_budget_height hWidth
      primitive c hPrimitive K _ _ _ _
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.sharedConstructionMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos le_rfl _ hs
      hOne hWidth
      primitive c hPrimitive K _ _ _ _

end Blotto.RationalPRGOriginalInput
