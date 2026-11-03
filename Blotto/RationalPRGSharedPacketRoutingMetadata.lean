import Blotto.RationalRoutingMetadata
import Blotto.RationalPRGRequestEntryConstructionMetadata

/-! Packet and cached-router metadata transfer through the actual primary
source handoff, retaining the same reader/cap. Packing scans, route payload
copies, physical addresses/backend/ownership and space remain separate. -/

namespace Blotto.RationalTerminalLotto

def packetRoutingMetadataWork {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (c : ℕ) : ℕ :=
  i.groupPacketMetadataWork primitive c + (RationalTerminalPacking.prepare i).routingMetadataWork primitive c

def packetRoutingMetadataBound (c n s : ℕ) : ℕ :=
  groupPacketMetadataBound c s + RationalTerminalPacking.routingMetadataBound c n s

theorem OnLattice.packetRoutingMetadataWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.packetRoutingMetadataWork primitive c ≤ packetRoutingMetadataBound c n s :=
  Nat.add_le_add (h.groupPacketMetadataWork_bound hD hB s hBudget hWidth primitive c hPrimitive)
    ((RationalTerminalPacking.prepare i).routingMetadataWork_bound primitive c hPrimitive D s h hD hB hWidth)

end Blotto.RationalTerminalLotto

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedPacketRoutingMetadataWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (c R : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits (fun value _ _ => (i.terminalData value).packetRoutingMetadataWork primitive c)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedPacketRoutingMetadataWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (_hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (R : ℕ) (bits : Fin R → Bool) :
    i.sharedPacketRoutingMetadataWork primitive c R bits ≤ RationalTerminalLotto.packetRoutingMetadataBound c n s := by
  let A := RationalTerminalLotto.packetRoutingMetadataBound c n s
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value _ _ => (i.terminalData value).packetRoutingMetadataWork primitive c) A 0
    (fun value hValue _ _ => ((h.terminalData value hValue).packetRoutingMetadataWork_bound
      hD hB s hBudget hWidth primitive c hPrimitive).trans (Nat.le_add_right _ _))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  have he : A + 0 * (R - 0) = A :=
    (congrArg (fun t : ℕ => A + t) (Nat.zero_mul (R - 0))).trans (Nat.add_zero A)
  exact hp.trans_eq he

noncomputable def sharedPaperPacketRoutingMetadataWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (c K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  i.sharedPacketRoutingMetadataWork primitive c (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))

end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedPacketRoutingMetadataWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.sharedPaperPacketRoutingMetadataWork primitive c K bits
  else i.normalizedInput.poorNativeSystem.sharedPaperPacketRoutingMetadataWork primitive c K bits

theorem selectedPacketRoutingMetadataWork_bound_of_inputWidth {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (s : ℕ) (hInput : 3 + i.originalInputWordWidth ≤ s) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedPacketRoutingMetadataWork primitive c rich K bits ≤ RationalTerminalLotto.packetRoutingMetadataBound c n s := by
  have hs : 2 ≤ s := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ s :=
    i.normalized_lattice_wordWidth_original.trans ((show 1 + i.originalInputWordWidth ≤ 3 + i.originalInputWordWidth by omega).trans hInput)
  have hOne : RationalHeight (1 : ℚ) s :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.sharedPacketRoutingMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le s hs (i.normalized_budget_height.mono hInput) hWidth
      primitive c hPrimitive _ _
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.sharedPacketRoutingMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos le_rfl s hs hOne hWidth primitive c hPrimitive _ _

end Blotto.RationalPRGOriginalInput
