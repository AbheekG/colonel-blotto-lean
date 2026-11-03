import Blotto.RationalGroupEntryConstructionMetadata
import Blotto.SharedTerminalWindowWork
import Blotto.RationalPRGOutputHeight

/-! Parent entry construction metadata transfers at the primary source
handoff. Original player input widths provide the terminal lattice and budget
bounds. Packed input derivation and output-route construction stay separate. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedEntryConstructionMetadataWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (c R : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits (fun value _ _ => (i.terminalData value).entryConstructionMetadataWork primitive c)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedEntryConstructionMetadataWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (R : ℕ) (bits : Fin R → Bool) :
    i.sharedEntryConstructionMetadataWork primitive c R bits ≤ RationalTerminalLotto.entryConstructionMetadataBound c s := by
  let A := RationalTerminalLotto.entryConstructionMetadataBound c s
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value _ _ => (i.terminalData value).entryConstructionMetadataWork primitive c) A 0
    (fun value hValue _ _ => ((h.terminalData value hValue).entryConstructionMetadataWork_bound
      hD hB s hs hBudget hWidth primitive c hPrimitive).trans (Nat.le_add_right _ _))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  have he : A + 0 * (R - 0) = A :=
    (congrArg (fun t : ℕ => A + t) (Nat.zero_mul (R - 0))).trans (Nat.add_zero A)
  exact hp.trans_eq he

noncomputable def sharedPaperEntryConstructionMetadataWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (c K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  i.sharedEntryConstructionMetadataWork primitive c (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))

end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedEntryConstructionMetadataWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.sharedPaperEntryConstructionMetadataWork primitive c K bits
  else i.normalizedInput.poorNativeSystem.sharedPaperEntryConstructionMetadataWork primitive c K bits

theorem selectedEntryConstructionMetadataWork_bound {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedEntryConstructionMetadataWork primitive c rich K bits ≤
      RationalTerminalLotto.entryConstructionMetadataBound c (3 + i.originalInputWordWidth) := by
  have hs : 2 ≤ 3 + i.originalInputWordWidth := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ 3 + i.originalInputWordWidth :=
    i.normalized_lattice_wordWidth_original.trans (by omega)
  have hOne : RationalHeight (1 : ℚ) (3 + i.originalInputWordWidth) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.sharedEntryConstructionMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le _ hs i.normalized_budget_height hWidth
      primitive c hPrimitive _ _
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.sharedEntryConstructionMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos le_rfl _ hs hOne hWidth primitive c hPrimitive _ _

end Blotto.RationalPRGOriginalInput
