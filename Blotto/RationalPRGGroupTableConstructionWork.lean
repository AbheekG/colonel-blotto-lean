import Blotto.RationalGroupTableConstructionWork
import Blotto.RationalPRGRequestComponentWork

/-! Cached group-table payload construction transfers through the primary
source handoff and both original-input players, then through the common request
gate. Full physical backend/time/ownership/space contracts remain separate. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedGroupTableConstructionWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits (fun value _ _ => (i.terminalData value).groupTableConstructionWork primitive)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedGroupTableConstructionWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (R : ℕ) (bits : Fin R → Bool) :
    i.sharedGroupTableConstructionWork primitive R bits ≤ RationalTerminalLotto.groupTableConstructionBound c n s := by
  let A := RationalTerminalLotto.groupTableConstructionBound c n s
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value _ _ => (i.terminalData value).groupTableConstructionWork primitive) A 0
    (fun value hValue _ _ => ((h.terminalData value hValue).groupTableConstructionWork_bound
      hD hB s hWidth primitive c hPrimitive).trans (Nat.le_add_right _ _))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  have he : A + 0 * (R - 0) = A :=
    (congrArg (fun t : ℕ => A + t) (Nat.zero_mul (R - 0))).trans (Nat.add_zero A)
  exact hp.trans_eq he

noncomputable def sharedPaperGroupTableConstructionWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  i.sharedGroupTableConstructionWork primitive (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))

end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedGroupTableConstructionWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.sharedPaperGroupTableConstructionWork primitive K bits
  else i.normalizedInput.poorNativeSystem.sharedPaperGroupTableConstructionWork primitive K bits

theorem selectedGroupTableConstructionWork_bound_of_inputWidth {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (s : ℕ) (hInput : 3 + i.originalInputWordWidth ≤ s) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedGroupTableConstructionWork primitive rich K bits ≤ RationalTerminalLotto.groupTableConstructionBound c n s := by
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ s :=
    i.normalized_lattice_wordWidth_original.trans ((show 1 + i.originalInputWordWidth ≤ 3 + i.originalInputWordWidth by omega).trans hInput)
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.sharedGroupTableConstructionWork_bound
      i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le s hWidth primitive c hPrimitive _ _
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.sharedGroupTableConstructionWork_bound
      i.normalizedInput.latticeDenominator_pos le_rfl s hWidth primitive c hPrimitive _ _

end Blotto.RationalPRGOriginalInput

namespace Blotto.RationalPRGBinaryRequest

noncomputable def groupTableConstructionWork (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  acceptedComponentWork (fun {n} i K bits =>
    RationalPRGOriginalInput.selectedGroupTableConstructionWork (n := n) i primitive rich K bits) frame seed

def groupTableConstructionFrameBound (c length : ℕ) : ℕ :=
  RationalTerminalLotto.groupTableConstructionBound c length (3 + (length + 2) * (4 * length + 13))

theorem groupTableConstructionWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    groupTableConstructionWork primitive rich frame seed ≤ groupTableConstructionFrameBound c frame.length := by
  apply acceptedComponentWork_incoming_bound
  intro input K bits hFields hInput _hK
  have hp := input.2.selectedGroupTableConstructionWork_bound_of_inputWidth primitive c hPrimitive _
    (Nat.add_le_add_left hInput 3) rich K bits
  exact hp.trans (RationalTerminalLotto.groupTableConstructionBound_mono_fields c _ hFields)

noncomputable def executionWithGroupTableConstructionWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithPackingCopyWork model primitive c copyResources rich frame seed + groupTableConstructionWork primitive rich frame seed

theorem executionWithGroupTableConstructionWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithGroupTableConstructionWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length + constructionMetadataFrameBound c frame.length +
              entryConstructionMetadataFrameBound c frame.length + packetRoutingMetadataFrameBound c frame.length +
                packingCopyFrameBound c frame.length + groupTableConstructionFrameBound c frame.length :=
  Nat.add_le_add (executionWithPackingCopyWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (groupTableConstructionWork_bound primitive c hPrimitive rich frame seed)

theorem groupTableConstructionWork_run_failure (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : groupTableConstructionWork primitive rich frame seed = 0 :=
  acceptedComponentWork_run_failure _ rich frame seed h

end Blotto.RationalPRGBinaryRequest
