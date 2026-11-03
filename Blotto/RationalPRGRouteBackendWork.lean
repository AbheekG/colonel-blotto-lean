import Blotto.RationalSharedRouteBackendWork
import Blotto.RationalPRGArrayRouteSampler

/-! Both original-budget players price the reached terminal route backend.
Input-derived denominator/width bounds discharge its promises. The same paper
bit blocks and primary source handoff are retained. Full cost composition and
allocator/whole-sampler peak-space contracts remain separate. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def paperRouteBackendWork {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let W := bitRouteSlotWidth n s
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedRouteBackendWork model primitive W (i.terminal_route_frameFit D s hD hB hLength hs hWidth)
    (ArrayStoreRAM.allocate (n * W) false ()) K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits) (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem OnLattice.paperRouteBackendWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperRouteBackendWork D s hD hB h.1 hs hWidth model primitive K bits ≤
      RationalTerminalLotto.terminalRouteBackendBound model c n s (bitRouteSlotWidth n s) :=
  h.sharedRouteBackendWork_bound hD hB s hs hWidth model primitive c _ hPrimitive _ _ K _ _ _ _

end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedRouteBackendWork {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let s := 3 + i.originalInputWordWidth
  let hWidth := i.normalized_lattice_wordWidth_original.trans (show 1 + i.originalInputWordWidth ≤ s by dsimp [s]; omega)
  if rich then i.normalizedInput.richNativeSystem.paperRouteBackendWork i.normalizedInput.latticeDenominator s
    i.normalizedInput.latticeDenominator_pos (le_refl _) i.normalizedInput.lengths_on_lattice (by dsimp [s]; omega) hWidth
    model primitive K bits
  else i.normalizedInput.poorNativeSystem.paperRouteBackendWork i.normalizedInput.latticeDenominator s
    i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le i.normalizedInput.lengths_on_lattice (by dsimp [s]; omega) hWidth
    model primitive K bits

theorem selectedRouteBackendWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedRouteBackendWork model primitive rich K bits ≤ RationalTerminalLotto.terminalRouteBackendBound model c n
      (3 + i.originalInputWordWidth) (RationalLottoResourceSystem.bitRouteSlotWidth n (3 + i.originalInputWordWidth)) := by
  have hs : 2 ≤ 3 + i.originalInputWordWidth := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ 3 + i.originalInputWordWidth :=
    i.normalized_lattice_wordWidth_original.trans (by omega)
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.paperRouteBackendWork_bound i.normalizedInput.latticeDenominator_pos
      i.normalizedInput.b_le _ hs hWidth model primitive c hPrimitive K bits
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.paperRouteBackendWork_bound i.normalizedInput.latticeDenominator_pos
      le_rfl _ hs hWidth model primitive c hPrimitive K bits

end Blotto.RationalPRGOriginalInput
