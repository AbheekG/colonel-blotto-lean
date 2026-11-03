import Blotto.RationalRouteArrayBackend
import Blotto.RationalTerminalBitRouteProgram

/-! The terminal sampler uses the streamed array-backed route region.
Exact program equality preserves all terminal outputs, fallbacks and budgets.
Native ownership and complete time/peak-space contracts remain separate. -/

namespace Blotto.RationalTerminalLotto

def programWithArrayRoutes {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : RationalAllocationProgram n 80 :=
  let packed := RationalTerminalPacking.prepare i
  let memory := (packed.runRouteArrayBackend W hFit state).cells.read
  match h : i.pivot with
  | none =>
    (((packed.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).mapped
      (fun y => (packed.emitFromBits memory y).allocation)).widen (by decide)
  | some pivot =>
    ((packed.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits).mapped
      (fun y => (packed.emitMixedFromBits memory pivot y).allocation)

theorem programWithArrayRoutes_eq_bit {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.programWithArrayRoutes W hFit state K outerBits scalarBits =
      i.programWithBitRoutes W hFit (ArrayStoreRAM.view state) K outerBits scalarBits := by
  let packed := RationalTerminalPacking.prepare i
  have hMemory := congrArg (fun s : TableStoreState (n * W) Bool β => s.cells) (packed.runRouteArrayBackend_refines W hFit state)
  change (packed.runRouteArrayBackend W hFit state).cells.read =
    (packed.runRouteBitStore W hFit (ArrayStoreRAM.view state)).cells at hMemory
  dsimp only [packed] at hMemory
  unfold programWithArrayRoutes programWithBitRoutes
  dsimp only
  rw [hMemory]
  rfl

theorem programWithArrayRoutes_eq {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.programWithArrayRoutes W hFit state K outerBits scalarBits = i.program K outerBits scalarBits :=
  (i.programWithArrayRoutes_eq_bit W hFit state K outerBits scalarBits).trans
    (i.programWithBitRoutes_eq W hFit (ArrayStoreRAM.view state) K outerBits scalarBits)

theorem programWithArrayRoutes_sample_fullBudget {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    FullBudget (i.B : ℝ) (fun j => ((i.programWithArrayRoutes W hFit state K outerBits scalarBits).sample R choiceBits j : ℝ)) := by
  rw [i.programWithArrayRoutes_eq]
  exact i.program_sample_fullBudget K R outerBits scalarBits choiceBits

end Blotto.RationalTerminalLotto
