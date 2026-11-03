import Blotto.BinaryRouteStoreProgram
import Blotto.TableStoreRAMMapping

/-! A bounded cached route program runs in a fixed binary region. It
initializes arbitrary starting bits and returns exactly the retained route
table on decoding. Encoding, address pricing and full sampler integration
remain separate from this store-program semantics/length contract. -/

namespace Blotto.RationalTerminalPacking

theorem routeStoreProgram_frameFit {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth D ≤ s) :
    ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ 2 * routePayloadWidth n s + 1 :=
  fun e he => BinaryRouteSlot.frame_fit_of_payload e.2 _ (p.routeStoreProgram_words D s h hD hB hs hWidth e he)

def routeBitStoreProgram {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) : List (Fin (n * W) × Bool) :=
  BinaryRouteStoreProgram.compile W p.routeStoreProgram hFit

def runRouteBitStore {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) : TableStoreState (n * W) Bool β :=
  TableStoreRAM.run (p.routeBitStoreProgram W hFit) state

theorem optionRouteStores_refines {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i)
    (state : TableStoreState n (Option (GroupRoute i.groups.length)) β) :
    (TableStoreRAM.run (BinaryRouteStoreProgram.optionAssignments p.routeStoreProgram) state).cells =
      (fun j => some (p.prepareOutput.table.read j)) := by
  let base : TableStoreState n (GroupRoute i.groups.length) β := ⟨fun _ => (none, 0), state.frame⟩
  have hFill : (TableStoreRAM.fillProgram (n := n) ((none, (0 : ℚ)) : GroupRoute i.groups.length)).map
      (fun e => (e.1, some e.2)) = TableStoreRAM.fillProgram (some ((none, (0 : ℚ)) : GroupRoute i.groups.length)) := by
    simp only [TableStoreRAM.fillProgram, List.map_ofFn]
    rfl
  unfold BinaryRouteStoreProgram.optionAssignments routeStoreProgram
  rw [List.map_append, hFill, TableStoreRAM.run_append, TableStoreRAM.run_fillProgram]
  change (TableStoreRAM.run (p.routeAssignments.map (fun e => (e.1, some e.2))) (TableStoreRAM.mapState some base)).cells = _
  rw [TableStoreRAM.run_mapState]
  have href := p.runRouteStore_refines base
  unfold runRouteStore routeStoreProgram at href
  rw [TableStoreRAM.run_append, TableStoreRAM.run_fillProgram] at href
  funext j
  change some ((TableStoreRAM.run p.routeAssignments base).cells j) = some (p.prepareOutput.table.read j)
  exact congrArg some (congrFun href j)

theorem runRouteBitStore_readback {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) :
    BinaryRouteStoreProgram.decodedCells i.groups.length (p.runRouteBitStore W hFit state).cells =
      (fun j => some (p.prepareOutput.table.read j)) :=
  (BinaryRouteStoreProgram.compile_decodes p.routeStoreProgram hFit state).trans
    (p.optionRouteStores_refines ⟨BinaryRouteStoreProgram.decodedCells i.groups.length state.cells, state.frame⟩)

theorem runRouteBitStore_frame {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) : (p.runRouteBitStore W hFit state).frame = state.frame := TableStoreRAM.run_frame _ _

theorem routeBitStoreProgram_length_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) :
    (p.routeBitStoreProgram W hFit).length ≤ 2 * n * W := by
  rw [routeBitStoreProgram, BinaryRouteStoreProgram.compile_length]
  have hCount : p.routeStoreProgram.length ≤ 2 * n := by
    rw [← TableStoreRAM.writeCount_eq]
    exact p.routeStoreProgram_writes
  exact Nat.mul_le_mul_right W hCount

theorem routeBitStoreProgram_wordWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (addressPrice : Fin (n * W) → ℕ) (A : ℕ) (hAddress : ∀ address, addressPrice address ≤ A) :
    TableStoreRAM.writeWordWork (fun _ : Bool => 1) addressPrice (p.routeBitStoreProgram W hFit) ≤ 2 * n * W * (2 + A) := by
  have hp := TableStoreRAM.writeWordWork_bound (fun _ : Bool => 1) addressPrice (p.routeBitStoreProgram W hFit) 1 A
    (fun _ _ => le_rfl) hAddress
  exact hp.trans (Nat.mul_le_mul_right _ (p.routeBitStoreProgram_length_bound W hFit))

end Blotto.RationalTerminalPacking
