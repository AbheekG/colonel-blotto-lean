import Blotto.RationalPackingMetadata
import Blotto.RationalRouteArrayCopyWork
import Blotto.RationalPRGRequestPacketRoutingMetadata

/-! Packing control and conservative route-payload copying transfer at the
primary shared source handoff. These include full-array copies, without an
in-place or exclusivity assumption. Physical backend and space remain separate. -/

namespace Blotto.RationalTerminalLotto

def packingCopyWork {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) : ℕ :=
  RationalPackingMetadata.packedWork primitive i.length i.B i.uniformItems +
    (RationalTerminalPacking.prepare i).routeArrayCopyWork

def packingCopyBound (c n s : ℕ) : ℕ :=
  RationalPackingMetadata.packedBound c n + RationalTerminalPacking.routeArrayCopyBound n s

theorem packingCopyBound_mono_fields (c s : ℕ) : Monotone (fun n => packingCopyBound c n s) := by
  intro a b hab
  exact Nat.add_le_add (RationalPackingMetadata.packedBound_mono_fields c hab)
    (RationalTerminalPacking.routeArrayCopyBound_mono_fields s hab)

theorem OnLattice.packingCopyWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.packingCopyWork primitive ≤ packingCopyBound c n s :=
  Nat.add_le_add (i.packingMetadataWork_bound primitive c hPrimitive)
    ((RationalTerminalPacking.prepare i).routeArrayCopyWork_bound D s h hD hB hs hWidth)

end Blotto.RationalTerminalLotto

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedPackingCopyWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits (fun value _ _ => (i.terminalData value).packingCopyWork primitive)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedPackingCopyWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (R : ℕ) (bits : Fin R → Bool) :
    i.sharedPackingCopyWork primitive R bits ≤ RationalTerminalLotto.packingCopyBound c n s := by
  let A := RationalTerminalLotto.packingCopyBound c n s
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value _ _ => (i.terminalData value).packingCopyWork primitive) A 0
    (fun value hValue _ _ => ((h.terminalData value hValue).packingCopyWork_bound
      hD hB s hs hWidth primitive c hPrimitive).trans (Nat.le_add_right _ _))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  have he : A + 0 * (R - 0) = A :=
    (congrArg (fun t : ℕ => A + t) (Nat.zero_mul (R - 0))).trans (Nat.add_zero A)
  exact hp.trans_eq he

noncomputable def sharedPaperPackingCopyWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  i.sharedPackingCopyWork primitive (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))

end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedPackingCopyWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.sharedPaperPackingCopyWork primitive K bits
  else i.normalizedInput.poorNativeSystem.sharedPaperPackingCopyWork primitive K bits

theorem selectedPackingCopyWork_bound_of_inputWidth {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (s : ℕ) (hInput : 3 + i.originalInputWordWidth ≤ s) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedPackingCopyWork primitive rich K bits ≤ RationalTerminalLotto.packingCopyBound c n s := by
  have hs : 2 ≤ s := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ s :=
    i.normalized_lattice_wordWidth_original.trans ((show 1 + i.originalInputWordWidth ≤ 3 + i.originalInputWordWidth by omega).trans hInput)
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.sharedPackingCopyWork_bound
      i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le s hs hWidth primitive c hPrimitive _ _
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.sharedPackingCopyWork_bound
      i.normalizedInput.latticeDenominator_pos le_rfl s hs hWidth primitive c hPrimitive _ _

end Blotto.RationalPRGOriginalInput
