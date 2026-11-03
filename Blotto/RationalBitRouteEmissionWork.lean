import Blotto.BinaryRouteSlotReadingWork
import Blotto.RationalBitRouteEmission

/-! Uniform emission prices actual decoded coefficient/value arguments,
plus one complete route-slot read per output coordinate. Primitive arithmetic
prices transfer by equality of these arguments, not by output equality alone.
Mixed-coordinate/address-formation/backend composition remains separate. -/

namespace Blotto.RationalTerminalPacking
open scoped BigOperators

def decodedCoordinateWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (model : RationalCostModel) (memory : Fin (n * W) → Bool) (y : Fin i.groups.length → ℚ) (j : Fin n) : ℕ :=
  let route := p.routeFromBits memory j
  match route.1 with
  | none => rationalWordWidth (0 : ℚ)
  | some g => rationalWordWidth route.2 + rationalWordWidth (y g) +
      model.rat (RationalExpression.pairWidth route.2 (y g)) + rationalWordWidth (route.2 * y g)

theorem decodedCoordinateWork_after_store {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (model : RationalCostModel) (y : Fin i.groups.length → ℚ) (j : Fin n) :
    p.decodedCoordinateWork model (p.runRouteBitStore W hFit state).cells y j = p.prepareOutput.routedBitCost model y j := by
  unfold decodedCoordinateWork PreparedGroupOutput.routedBitCost
  rw [p.routeFromBits_after_store W hFit state j]
  cases ht : (p.prepareOutput.table.read j).1 <;> simp only [ht]

def uniformBitEmissionWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (model : RationalCostModel) (primitive : ℕ → ℕ) (memory : Fin (n * W) → Bool) (y : Fin i.groups.length → ℚ) : ℕ :=
  p.emissionRouteReadingWork model primitive memory + (∑ g, rationalWordWidth (y g)) +
    ∑ j : Fin n, p.decodedCoordinateWork model memory y j

theorem uniformBitEmissionWork_bound {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) (state : TableStoreState (n * W) Bool β)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (y : Fin i.groups.length → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCoefficients : ∀ j, RationalHeight (p.prepareOutput.table.read j).2 s) (hY : ∀ g, RationalHeight (y g) s) :
    p.uniformBitEmissionWork model primitive (p.runRouteBitStore W hFit state).cells y ≤
      n * BinaryRouteSlot.readingBound model c n i.groups.length W +
        (i.groups.length + 4 * n) * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hRead := p.emissionRouteReadingWork_bound model primitive c hPrimitive (p.runRouteBitStore W hFit state).cells
  have hArithmetic := p.prepareOutput.emitBitCost_bound model y s hs hCoefficients hY
  have hCoordinates : (∑ j : Fin n, p.decodedCoordinateWork model (p.runRouteBitStore W hFit state).cells y j) =
      ∑ j : Fin n, p.prepareOutput.routedBitCost model y j := by
    apply Finset.sum_congr rfl
    intro j _
    exact p.decodedCoordinateWork_after_store W hFit state model y j
  unfold uniformBitEmissionWork
  rw [hCoordinates]
  unfold PreparedGroupOutput.emitBitCost at hArithmetic
  omega

def decodedRoutedValue {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (memory : Fin (n * W) → Bool) (y : Fin i.groups.length → ℚ) (j : Fin n) : ℚ :=
  let route := p.routeFromBits memory j
  match route.1 with | none => 0 | some g => route.2 * y g

theorem decodedRoutedValue_after_store {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (y : Fin i.groups.length → ℚ) (j : Fin n) :
    p.decodedRoutedValue (p.runRouteBitStore W hFit state).cells y j = p.prepareOutput.routedValue y j := by
  unfold decodedRoutedValue PreparedGroupOutput.routedValue
  rw [p.routeFromBits_after_store W hFit state j]
  cases ht : (p.prepareOutput.table.read j).1 <;> simp only [ht]

def mixedDecodedCoordinateWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (model : RationalCostModel) (memory : Fin (n * W) → Bool) (pivot : Fin n)
    (y : Fin (i.groups.length + 1) → ℚ) (j : Fin n) : ℕ :=
  let base := p.decodedRoutedValue memory (fun g => y g.castSucc) j
  let extra := if j = pivot then y (Fin.last i.groups.length) else 0
  p.decodedCoordinateWork model memory (fun g => y g.castSucc) j + rationalWordWidth base + rationalWordWidth extra +
    model.rat (RationalExpression.pairWidth base extra) + rationalWordWidth (base + extra)

theorem mixedDecodedCoordinateWork_after_store {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (model : RationalCostModel) (pivot : Fin n)
    (y : Fin (i.groups.length + 1) → ℚ) (j : Fin n) :
    p.mixedDecodedCoordinateWork model (p.runRouteBitStore W hFit state).cells pivot y j =
      p.prepareOutput.mixedCoordinateBitCost model pivot y j := by
  unfold mixedDecodedCoordinateWork PreparedGroupOutput.mixedCoordinateBitCost
  rw [p.decodedRoutedValue_after_store W hFit state, p.decodedCoordinateWork_after_store W hFit state]

def mixedBitEmissionWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (model : RationalCostModel) (primitive : ℕ → ℕ) (memory : Fin (n * W) → Bool) (pivot : Fin n)
    (y : Fin (i.groups.length + 1) → ℚ) : ℕ :=
  p.emissionRouteReadingWork model primitive memory + (∑ g, rationalWordWidth (y g)) +
    ∑ j : Fin n, p.mixedDecodedCoordinateWork model memory pivot y j

theorem mixedBitEmissionWork_bound {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) (state : TableStoreState (n * W) Bool β)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (pivot : Fin n) (y : Fin (i.groups.length + 1) → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCoefficients : ∀ j, RationalHeight (p.prepareOutput.table.read j).2 s) (hY : ∀ g, RationalHeight (y g) s) :
    p.mixedBitEmissionWork model primitive (p.runRouteBitStore W hFit state).cells pivot y ≤
      n * BinaryRouteSlot.readingBound model c n i.groups.length W +
        (i.groups.length + 1 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hRead := p.emissionRouteReadingWork_bound model primitive c hPrimitive (p.runRouteBitStore W hFit state).cells
  have hArithmetic := p.prepareOutput.emitMixedBitCost_bound model pivot y s hs hCoefficients hY
  have hCoordinates : (∑ j : Fin n, p.mixedDecodedCoordinateWork model (p.runRouteBitStore W hFit state).cells pivot y j) =
      ∑ j : Fin n, p.prepareOutput.mixedCoordinateBitCost model pivot y j := by
    apply Finset.sum_congr rfl
    intro j _
    exact p.mixedDecodedCoordinateWork_after_store W hFit state model pivot y j
  unfold mixedBitEmissionWork
  rw [hCoordinates]
  unfold PreparedGroupOutput.emitMixedBitCost at hArithmetic
  omega

end Blotto.RationalTerminalPacking
