import Blotto.RationalRouteBitStore
import Blotto.PreparedGroupEmissionCost

/-! Emission reads the stored binary route records and produces a whole
allocation. After the verified route build, both uniform and mixed emitters
equal the retained prepared emitter exactly. Decoder/primitive work is separate. -/

namespace Blotto.RationalTerminalPacking

def routeFromBits {n : ℕ} {i : RationalTerminalLotto n} (_p : RationalTerminalPacking i) {W : ℕ}
    (memory : Fin (n * W) → Bool) (j : Fin n) : GroupRoute i.groups.length :=
  (BinaryRouteStoreProgram.decodedCells i.groups.length memory j).getD (none, 0)

theorem routeFromBits_after_store {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (j : Fin n) :
    p.routeFromBits (p.runRouteBitStore W hFit state).cells j = p.prepareOutput.table.read j := by
  have hp := congrFun (p.runRouteBitStore_readback W hFit state) j
  unfold routeFromBits
  rw [hp]
  rfl

def emitFromBits {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (memory : Fin (n * W) → Bool) (y : Fin i.groups.length → ℚ) : RationalResourceArray n :=
  RationalResourceArray.ofAllocation (fun j =>
    let route := p.routeFromBits memory j
    match route.1 with
    | none => 0
    | some g => route.2 * y g)

def emitMixedFromBits {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (memory : Fin (n * W) → Bool) (pivot : Fin n) (y : Fin (i.groups.length + 1) → ℚ) : RationalResourceArray n :=
  RationalResourceArray.ofAllocation (fun j =>
    (let route := p.routeFromBits memory j
     match route.1 with | none => 0 | some g => route.2 * y g.castSucc) +
      if j = pivot then y (Fin.last i.groups.length) else 0)

theorem emitFromBits_after_store {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (y : Fin i.groups.length → ℚ) :
    (p.emitFromBits (p.runRouteBitStore W hFit state).cells y).allocation = (p.prepareOutput.emit y).allocation := by
  funext j
  simp only [emitFromBits, PreparedGroupOutput.emit, RationalProportionalGroups.emit,
    RationalResourceArray.allocation_ofAllocation, FixedArrayTable.read_ofFn]
  rw [p.routeFromBits_after_store W hFit state j]
  cases (p.prepareOutput.table.read j).1 <;> simp only

theorem emitMixedFromBits_after_store {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (pivot : Fin n) (y : Fin (i.groups.length + 1) → ℚ) :
    (p.emitMixedFromBits (p.runRouteBitStore W hFit state).cells pivot y).allocation = (p.prepareOutput.emitMixed pivot y).allocation := by
  funext j
  simp only [emitMixedFromBits, PreparedGroupOutput.emitMixed, RationalProportionalGroups.emitMixed,
    RationalResourceArray.allocation_ofAllocation, FixedArrayTable.read_ofFn]
  rw [p.routeFromBits_after_store W hFit state j]
  cases (p.prepareOutput.table.read j).1 <;> simp only

theorem emitFromBits_fullBudget {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (y : Fin i.groups.length → ℚ)
    (hy : FullBudget (i.B : ℝ) (fun g => (y g : ℝ))) :
    FullBudget (i.B : ℝ) (p.emitFromBits (p.runRouteBitStore W hFit state).cells y).realAllocation := by
  change FullBudget (i.B : ℝ) (fun j => ((p.emitFromBits (p.runRouteBitStore W hFit state).cells y).allocation j : ℝ))
  rw [p.emitFromBits_after_store W hFit state y]
  exact p.prepareOutput.emit_fullBudget hy

theorem emitMixedFromBits_fullBudget {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i) (W : ℕ)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (pivot : Fin n) (y : Fin (i.groups.length + 1) → ℚ)
    (hy : FullBudget (i.B : ℝ) (fun g => (y g : ℝ))) :
    FullBudget (i.B : ℝ) (p.emitMixedFromBits (p.runRouteBitStore W hFit state).cells pivot y).realAllocation := by
  change FullBudget (i.B : ℝ) (fun j => ((p.emitMixedFromBits (p.runRouteBitStore W hFit state).cells pivot y).allocation j : ℝ))
  rw [p.emitMixedFromBits_after_store W hFit state pivot y]
  exact p.prepareOutput.emitMixed_fullBudget pivot hy

end Blotto.RationalTerminalPacking
