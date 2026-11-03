import Blotto.FixedRegionFormedAddressWork
import Blotto.RationalTerminalArrayRouteProgram
import Blotto.RationalTerminalGroupInputCost

/-! One terminal route build precedes the selected cached group execution.
Route reads/address formation are charged only when emission occurs, at the
actual cap/position. Existing rational output arithmetic stays separately
priced; whole-allocator/backend interpretation remains an explicit contract. -/

namespace Blotto.BinaryRouteSlot

theorem readingBound_mono_groups (model : RationalCostModel) (c n W : ℕ) {m M : ℕ} (h : m ≤ M) :
    readingBound model c n m W ≤ readingBound model c n M W := by
  have hm := binaryWordWidth_mono h
  have hPrice := Nat.mul_le_mul_left (1 + c) (Nat.add_le_add_left hm (W + 1))
  unfold readingBound BinaryRouteFrame.decodingBound
  omega

end Blotto.BinaryRouteSlot

namespace Blotto.RationalTerminalLotto
open scoped BigOperators

theorem optionConstantWork_bound {α : Type*} (result : Option α) (price bound : ℕ) (h : price ≤ bound) :
    (result.map (fun _ => price)).getD 0 ≤ bound := by
  cases result with
  | none => exact Nat.zero_le _
  | some value => exact h

def routeReadFormationWork {n : ℕ} (i : RationalTerminalLotto n) {W : ℕ}
    (model : RationalCostModel) (primitive : ℕ → ℕ) (memory : Fin (n * W) → Bool) : ℕ :=
  (RationalTerminalPacking.prepare i).emissionRouteReadingWork model primitive memory +
    ∑ j : Fin n, BinaryRouteSlot.formationWork (W := W) primitive j

def routeReadFormationBound (model : RationalCostModel) (c n W : ℕ) : ℕ :=
  n * BinaryRouteSlot.readingBound model c n 3 W + n * W * BinaryAddressFormation.encodedWorkBound c 0 n W

theorem routeReadFormationWork_bound {n W : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (memory : Fin (n * W) → Bool) :
    i.routeReadFormationWork model primitive memory ≤ routeReadFormationBound model c n W := by
  have hGroups : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  have hRead := ((RationalTerminalPacking.prepare i).emissionRouteReadingWork_bound model primitive c hPrimitive memory).trans
    (Nat.mul_le_mul_left n (BinaryRouteSlot.readingBound_mono_groups model c n W hGroups))
  have hForms : (∑ j : Fin n, BinaryRouteSlot.formationWork (W := W) primitive j) ≤
      n * (W * BinaryAddressFormation.encodedWorkBound c 0 n W) := by
    calc
      _ ≤ ∑ _j : Fin n, W * BinaryAddressFormation.encodedWorkBound c 0 n W := Finset.sum_le_sum (fun j _ =>
        BinaryRouteSlot.formationWork_bound primitive c hPrimitive j)
      _ = _ := by simp
  unfold routeReadFormationWork routeReadFormationBound
  nlinarith

def terminalRouteBackendWork {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (W : ℕ) (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let packed := RationalTerminalPacking.prepare i
  let memory := (packed.runRouteArrayBackend W hFit state).cells.read
  packed.routeBitBuildWithFormedAddresses primitive W hFit +
    match h : i.pivot with
    | none =>
      let group := (packed.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits
      group.machine.cachedEmissionWork (fun _ => i.routeReadFormationWork model primitive memory) N bits (.state group.start) pos hpos
    | some pivot =>
      let group := (packed.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits
      group.machine.cachedEmissionWork (fun _ => i.routeReadFormationWork model primitive memory) N bits (.state group.start) pos hpos

def terminalRouteBackendBound (model : RationalCostModel) (c n s W : ℕ) : ℕ :=
  RationalTerminalPacking.routeBitBuildBound c n s W (FixedWordRegion.formedAccessBound c n W) + routeReadFormationBound model c n W

theorem OnLattice.terminalRouteBackendWork_bound {n : ℕ} {β : Type*} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c W : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalRouteBackendWork model primitive W hFit state K outerBits scalarBits N bits pos hpos ≤
      terminalRouteBackendBound model c n s W := by
  let packed := RationalTerminalPacking.prepare i
  have hBuild := packed.routeBitBuildWithFormedAddresses_bound D s h hD hB hs hWidth primitive c W hPrimitive hFit
  have hReads := i.routeReadFormationWork_bound model primitive c hPrimitive (packed.runRouteArrayBackend W hFit state).cells.read
  dsimp only [packed] at hBuild hReads
  unfold terminalRouteBackendWork
  dsimp only
  split
  · rw [WordStateMachine.cachedEmissionWork_eq]
    exact Nat.add_le_add hBuild (optionConstantWork_bound _ _ _ hReads)
  · rw [WordStateMachine.cachedEmissionWork_eq]
    exact Nat.add_le_add hBuild (optionConstantWork_bound _ _ _ hReads)

end Blotto.RationalTerminalLotto
