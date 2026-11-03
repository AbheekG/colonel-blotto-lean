import Blotto.BinaryRouteArrayStore

/-! Cached route construction has an array-backed streamed entry point.
Readback and frame/capacity equal the checked RAM semantics. The peak payload
observer includes one slot word, address/bit assignments and simultaneous copy
buffers; complete physical allocator and whole-sampler space remain separate. -/

namespace Blotto.RationalTerminalPacking

def runRouteArrayBackend {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) : ArrayStoreState (n * W) Bool β :=
  BinaryRouteArrayStore.runStream W p.routeStoreProgram hFit state

theorem runRouteArrayBackend_refines {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) :
    ArrayStoreRAM.view (p.runRouteArrayBackend W hFit state) = p.runRouteBitStore W hFit (ArrayStoreRAM.view state) :=
  BinaryRouteArrayStore.runStream_refines p.routeStoreProgram hFit state

theorem runRouteArrayBackend_readback {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) :
    BinaryRouteStoreProgram.decodedCells i.groups.length (p.runRouteArrayBackend W hFit state).cells.read =
      (fun j => some (p.prepareOutput.table.read j)) := by
  have hp := congrArg (fun s : TableStoreState (n * W) Bool β => s.cells) (p.runRouteArrayBackend_refines W hFit state)
  change (p.runRouteArrayBackend W hFit state).cells.read = (p.runRouteBitStore W hFit (ArrayStoreRAM.view state)).cells at hp
  rw [hp]
  exact p.runRouteBitStore_readback W hFit (ArrayStoreRAM.view state)

theorem runRouteArrayBackend_region {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) :
    (p.runRouteArrayBackend W hFit state).cells.data.size = n * W ∧ (p.runRouteArrayBackend W hFit state).frame = state.frame :=
  BinaryRouteArrayStore.runStream_region p.routeStoreProgram hFit state

def routeArrayBackendPeakPayload {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (external : ℕ) : ℕ :=
  BinaryRouteArrayStore.peakStorePayloadWords W p.routeStoreProgram hFit state external

theorem routeArrayBackendPeakPayload_bound {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (external : ℕ) :
    p.routeArrayBackendPeakPayload W hFit state external ≤
      external + W * (FixedWordRegion.addressWidth 0 n W + 3) + 2 * n * W + 1 :=
  BinaryRouteArrayStore.peakStorePayloadWords_bound p.routeStoreProgram hFit state external

end Blotto.RationalTerminalPacking
