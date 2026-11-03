import Blotto.BinaryRouteArrayCopyExecution
import Blotto.RationalPRGLedgerPolynomial
import Blotto.RationalPRGArrayRouteRequest

/-! Conservative payload-copy RAM costs follow the actual streamed bit-array
route builder, including its fixed-array initialization. The reached compiler
is charged once at the primary source handoff and lifts to both player/request
paths. Encoding/address/control prices compose with this copying component;
full rational primitive, execution, allocator and peak-space contracts remain
separate. No compiler or GC implementation is asserted. -/

namespace Blotto.RationalTerminalPacking

def runRouteArrayBackendWithCopyWork {n : ℕ} {i : RationalTerminalLotto n} {β : Type*}
    (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) : ArrayStoreState (n * W) Bool β × ℕ :=
  BinaryRouteArrayStore.runStreamWithCopyWork W p.routeStoreProgram hFit state

theorem runRouteArrayBackendWithCopyWork_state {n : ℕ} {i : RationalTerminalLotto n} {β : Type*}
    (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) :
    (p.runRouteArrayBackendWithCopyWork W hFit state).1 = p.runRouteArrayBackend W hFit state :=
  BinaryRouteArrayStore.runStreamWithCopyWork_state p.routeStoreProgram hFit state

theorem runRouteArrayBackendWithCopyWork_bound {n : ℕ} {i : RationalTerminalLotto n} {β : Type*}
    (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) :
    (p.runRouteArrayBackendWithCopyWork W hFit state).2 ≤ 4 * n * W * (n * W + 1) := by
  have h := BinaryRouteArrayStore.runStreamWithCopyWork_bound p.routeStoreProgram hFit state
  have hCount : p.routeStoreProgram.length ≤ 2 * n := by
    rw [← TableStoreRAM.writeCount_eq]
    exact p.routeStoreProgram_writes
  exact h.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right W hCount)).trans_eq (by ring))

def allocatedRouteArrayCopyBound (n W : ℕ) : ℕ := 2 * n * W + 4 * n * W * (n * W + 1)

def allocateRouteArrayBackendWithCopyWork {n : ℕ} {i : RationalTerminalLotto n} {β : Type*}
    (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) (frame : β) :
    ArrayStoreState (n * W) Bool β × ℕ :=
  BinaryRouteArrayStore.allocateRunStreamWithCopyWork W p.routeStoreProgram hFit frame

theorem allocateRouteArrayBackendWithCopyWork_state {n : ℕ} {i : RationalTerminalLotto n} {β : Type*}
    (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) (frame : β) :
    (p.allocateRouteArrayBackendWithCopyWork W hFit frame).1 =
      p.runRouteArrayBackend W hFit (ArrayStoreRAM.allocate (n * W) false frame) :=
  BinaryRouteArrayStore.allocateRunStreamWithCopyWork_state p.routeStoreProgram hFit frame

theorem allocateRouteArrayBackendWithCopyWork_readback {n : ℕ} {i : RationalTerminalLotto n} {β : Type*}
    (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) (frame : β) :
    BinaryRouteStoreProgram.decodedCells i.groups.length
      (p.allocateRouteArrayBackendWithCopyWork W hFit frame).1.cells.read =
        (fun j => some (p.prepareOutput.table.read j)) := by
  rw [p.allocateRouteArrayBackendWithCopyWork_state]
  exact p.runRouteArrayBackend_readback W hFit _

theorem allocateRouteArrayBackendWithCopyWork_bound {n : ℕ} {i : RationalTerminalLotto n} {β : Type*}
    (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) (frame : β) :
    (p.allocateRouteArrayBackendWithCopyWork W hFit frame).2 ≤ allocatedRouteArrayCopyBound n W := by
  have h := p.runRouteArrayBackendWithCopyWork_bound W hFit (ArrayStoreRAM.allocate (n * W) false frame)
  unfold allocateRouteArrayBackendWithCopyWork BinaryRouteArrayStore.allocateRunStreamWithCopyWork
  simp only [ArrayStoreRAM.allocateWithCopyWork, Nat.mul_one]
  change 2 * (n * W) + (p.runRouteArrayBackendWithCopyWork W hFit
      (ArrayStoreRAM.allocate (n * W) false frame)).2 ≤ allocatedRouteArrayCopyBound n W
  unfold allocatedRouteArrayCopyBound
  exact (Nat.add_le_add_left h _).trans_eq (by ring)

def allocatedRouteArrayBuildWork {n : ℕ} {i : RationalTerminalLotto n}
    (p : RationalTerminalPacking i) (primitive : ℕ → ℕ) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) : ℕ :=
  p.routeBitBuildWithFormedAddresses primitive W hFit +
    (p.allocateRouteArrayBackendWithCopyWork W hFit ()).2

theorem allocatedRouteArrayBuildWork_bound {n : ℕ} {i : RationalTerminalLotto n}
    (p : RationalTerminalPacking i) (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1)
    (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (primitive : ℕ → ℕ) (c W : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) :
    p.allocatedRouteArrayBuildWork primitive W hFit ≤
      routeBitBuildBound c n s W (FixedWordRegion.formedAccessBound c n W) + allocatedRouteArrayCopyBound n W :=
  Nat.add_le_add (p.routeBitBuildWithFormedAddresses_bound D s h hD hB hs hWidth primitive c W hPrimitive hFit)
    (p.allocateRouteArrayBackendWithCopyWork_bound W hFit ())

theorem allocatedRouteArrayCopyBound_mono {n N W V : ℕ} (hn : n ≤ N) (hW : W ≤ V) :
    allocatedRouteArrayCopyBound n W ≤ allocatedRouteArrayCopyBound N V := by
  unfold allocatedRouteArrayCopyBound
  gcongr

end Blotto.RationalTerminalPacking

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedRouteArrayCopyWork {n : ℕ} (i : RationalLottoResourceSystem n) (W : ℕ)
    (hFit : ∀ value : i.PhaseResult, ∀ e ∈ (RationalTerminalPacking.prepare (i.terminalData value)).routeStoreProgram,
      (BinaryRouteFrame.encode e.2).length ≤ W) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits
    (fun value _pos _hpos => ((RationalTerminalPacking.prepare (i.terminalData value)).allocateRouteArrayBackendWithCopyWork
      W (hFit value) ()).2)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedRouteArrayCopyWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (W : ℕ)
    (hFit : ∀ value : i.PhaseResult, ∀ e ∈ (RationalTerminalPacking.prepare (i.terminalData value)).routeStoreProgram,
      (BinaryRouteFrame.encode e.2).length ≤ W) (R : ℕ) (bits : Fin R → Bool) :
    i.sharedRouteArrayCopyWork W hFit R bits ≤ RationalTerminalPacking.allocatedRouteArrayCopyBound n W := by
  let A := RationalTerminalPacking.allocatedRouteArrayCopyBound n W
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value _pos _hpos => ((RationalTerminalPacking.prepare (i.terminalData value)).allocateRouteArrayBackendWithCopyWork
      W (hFit value) ()).2) A 0
    (fun value _hValue _pos _hpos =>
      ((RationalTerminalPacking.prepare (i.terminalData value)).allocateRouteArrayBackendWithCopyWork_bound W (hFit value) ()).trans
        (Nat.le_add_right _ _))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  exact hp.trans_eq ((congrArg (fun t : ℕ => A + t) (Nat.zero_mul (R - 0))).trans (Nat.add_zero A))

noncomputable def paperRouteArrayCopyWork {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hLength : ∀ j, OnRationalLattice D (i.length j))
    (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedRouteArrayCopyWork (bitRouteSlotWidth n s) (i.terminal_route_frameFit D s hD hB hLength hs hWidth)
    (coinBitBudget n K) (firstBitBlock (coinBitBudget n K) K inner)

theorem OnLattice.paperRouteArrayCopyWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperRouteArrayCopyWork D s hD hB h.1 hs hWidth K bits ≤
      RationalTerminalPacking.allocatedRouteArrayCopyBound n (bitRouteSlotWidth n s) :=
  h.sharedRouteArrayCopyWork_bound _ _ _ _

end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedRouteArrayCopyWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let s := 3 + i.originalInputWordWidth
  let hWidth := i.normalized_lattice_wordWidth_original.trans (show 1 + i.originalInputWordWidth ≤ s by dsimp [s]; omega)
  if rich then i.normalizedInput.richNativeSystem.paperRouteArrayCopyWork i.normalizedInput.latticeDenominator s
    i.normalizedInput.latticeDenominator_pos (le_refl _) i.normalizedInput.lengths_on_lattice (by dsimp [s]; omega) hWidth K bits
  else i.normalizedInput.poorNativeSystem.paperRouteArrayCopyWork i.normalizedInput.latticeDenominator s
    i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le i.normalizedInput.lengths_on_lattice (by dsimp [s]; omega) hWidth K bits

theorem selectedRouteArrayCopyWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedRouteArrayCopyWork rich K bits ≤ RationalTerminalPacking.allocatedRouteArrayCopyBound n
      (RationalLottoResourceSystem.bitRouteSlotWidth n (3 + i.originalInputWordWidth)) := by
  have hs : 2 ≤ 3 + i.originalInputWordWidth := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ 3 + i.originalInputWordWidth :=
    i.normalized_lattice_wordWidth_original.trans (by omega)
  cases rich with
  | false =>
      exact i.normalizedInput.poorNativeSystem_on_lattice.paperRouteArrayCopyWork_bound
        i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le _ hs hWidth K bits
  | true =>
      exact i.normalizedInput.richNativeSystem_on_lattice.paperRouteArrayCopyWork_bound
        i.normalizedInput.latticeDenominator_pos le_rfl _ hs hWidth K bits

end Blotto.RationalPRGOriginalInput

namespace Blotto.RationalPRGBinaryRequest

noncomputable def routeArrayCopyWork (rich : Bool) (frame seed : List Bool) : ℕ :=
  acceptedComponentWork (fun {n} i K bits => RationalPRGOriginalInput.selectedRouteArrayCopyWork (n := n) i rich K bits) frame seed

def routeArrayCopyFrameBound (length : ℕ) : ℕ :=
  let s := 3 + (length + 2) * (4 * length + 13)
  RationalTerminalPacking.allocatedRouteArrayCopyBound length (RationalLottoResourceSystem.bitRouteSlotWidth length s)

theorem routeArrayCopyWork_frame_bound (rich : Bool) (frame seed : List Bool) :
    routeArrayCopyWork rich frame seed ≤ routeArrayCopyFrameBound frame.length := by
  apply acceptedComponentWork_incoming_bound
  intro input K bits hN hInput _hK
  have hWord : 3 + input.2.originalInputWordWidth ≤ 3 + (frame.length + 2) * (4 * frame.length + 13) := by omega
  exact (input.2.selectedRouteArrayCopyWork_bound rich K bits).trans
    (RationalTerminalPacking.allocatedRouteArrayCopyBound_mono hN
      (RationalLottoResourceSystem.bitRouteSlotWidth_mono hN hWord))

theorem routeArrayCopyWork_run_failure (rich : Bool) (frame seed : List Bool)
    (h : runArrayRoutes rich frame seed = none) : routeArrayCopyWork rich frame seed = 0 :=
  acceptedComponentWork_run_failure _ rich frame seed ((runArrayRoutes_eq rich frame seed).symm.trans h)

noncomputable def executionWithRouteArrayCopyWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithRouteBackendWork model primitive c copyResources rich frame seed + routeArrayCopyWork rich frame seed

theorem executionWithRouteArrayCopyWork_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithRouteArrayCopyWork model primitive c copyResources rich frame seed ≤
      completeLedgerFrameBound model c copyResources frame.length seed.length + routeArrayCopyFrameBound frame.length :=
  Nat.add_le_add (executionWithRouteBackendWork_complete_bound model primitive c hPrimitive copyResources rich frame seed)
    (routeArrayCopyWork_frame_bound rich frame seed)

theorem routeArrayCopyFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => routeArrayCopyFrameBound x.2.1) := by
  simp only [routeArrayCopyFrameBound, RationalTerminalPacking.allocatedRouteArrayCopyBound,
    RationalLottoResourceSystem.bitRouteSlotWidth, RationalTerminalPacking.routePayloadWidth]
  polynomial_envelope

theorem executionWithRouteArrayCopyWork_polynomial :
    ∃ C d : ℕ, ∀ (primitive : ℕ → ℕ) (c : ℕ),
      (∀ w, primitive w ≤ c * w) → ∀ (copyResources rich : Bool) (frame seed : List Bool),
      executionWithRouteArrayCopyWork RationalCostModel.schoolbook primitive c copyResources rich frame seed ≤
        C * (c + frame.length + seed.length + 1) ^ d := by
  have hBoth := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add (completeLedgerFrameBound_polynomial false)
      (completeLedgerFrameBound_polynomial true)) routeArrayCopyFrameBound_polynomial
  rcases hBoth with ⟨C, d, hBoth⟩
  refine ⟨C, d, ?_⟩
  intro primitive c hPrimitive copyResources rich frame seed
  have hCost := executionWithRouteArrayCopyWork_frame_bound RationalCostModel.schoolbook
    primitive c hPrimitive copyResources rich frame seed
  have hSum := hBoth (c, frame.length, seed.length)
  have hSelect : completeLedgerFrameBound RationalCostModel.schoolbook c copyResources frame.length seed.length ≤
      completeLedgerFrameBound RationalCostModel.schoolbook c false frame.length seed.length +
        completeLedgerFrameBound RationalCostModel.schoolbook c true frame.length seed.length := by
    cases copyResources <;> omega
  simpa only [ledgerInputSize, Nat.add_assoc] using
    hCost.trans ((Nat.add_le_add_right hSelect _).trans hSum)

end Blotto.RationalPRGBinaryRequest
