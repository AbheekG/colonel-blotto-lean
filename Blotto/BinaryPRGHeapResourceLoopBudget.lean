import Blotto.BinaryPRGHeapResourceLoop

/-! An invariant-indexed whole-run cost theorem for the physical resource loop.
The step budget is stated on actual pair, coin and selected tape operations;
instantiating it from original input widths and a preserved heap reservation
is a separate obligation. -/

namespace Blotto.BinaryPRGHeapResourceLoopBudget
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

structure ReachableStepBudget (seed : BinarySeedLookupTree.Store)
    (limits : Stored capacity.tree) (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) : Prop where
  pairCoin : ∀ (state : Finished capacity n hCount)
      (first second : Address capacity.width capacity.cap)
      (tail : List (Address capacity.width capacity.cap))
      (he : state.active = first :: second :: tail)
      (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
      Inv state →
      let prepared := BinaryPRGHeapResourceLoop.pairWithWork
        (hC := hC) limits state first second tail he
      prepared.2 +
        (BinaryWordIndexCoinController.sample seed prepared.1.probability pc hp).2 + 8 ≤ M
  selected : ∀ (state : Finished capacity n hCount)
      (first second : Address capacity.width capacity.cap)
      (tail : List (Address capacity.width capacity.cap))
      (he : state.active = first :: second :: tail) (branch : Bool),
      Inv state →
      (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1
        (BinaryPRGHeapResourceLoop.pairWithWork_value
          (hC := hC) limits state first second tail he) branch).2 ≤ M
  closed : ∀ (state : Finished capacity n hCount)
      (first second : Address capacity.width capacity.cap)
      (tail : List (Address capacity.width capacity.cap))
      (he : state.active = first :: second :: tail) (branch : Bool),
      Inv state →
      Inv (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1
        (BinaryPRGHeapResourceLoop.pairWithWork_value
          (hC := hC) limits state first second tail he) branch).1

theorem runWithWork_bound (seed : BinarySeedLookupTree.Store)
    (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ)
    (budget : ReachableStepBudget seed limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 ≤
      state.active.length * (2 * M) + 2 := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount)
      (q : FixedBinaryWord seed.width) (hq : q.value ≤ seed.cap.value),
      Inv s → s.active.length ≤ fuel →
      (BinaryPRGHeapResourceLoop.runWithWork seed limits hC s q hq).2 ≤
        fuel * (2 * M) + 2 from
    h state.active.length state pc hp hInv le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s q hq hInvariant hSize
      conv_lhs => unfold BinaryPRGHeapResourceLoop.runWithWork
      split
      · rename_i first second tail he
        let prepared := BinaryPRGHeapResourceLoop.pairWithWork
          (hC := hC) limits s first second tail he
        let coin := BinaryWordIndexCoinController.sample seed prepared.1.probability q hq
        have hPair := budget.pairCoin s first second tail he q hq hInvariant
        change prepared.2 + coin.2 + 8 ≤ M at hPair
        dsimp only
        split
        · rename_i _ hCoin
          change prepared.2 + coin.2 + 4 ≤ fuel * (2 * M) + 2
          have hPositive : 1 ≤ fuel := by
            have hTwo : 2 ≤ s.active.length := by rw [he]; simp
            omega
          have hMul := Nat.mul_le_mul_right (2 * M) hPositive
          omega
        · rename_i _ branch hCoin
          let selected := BinaryPRGHeapResourceLoop.selectWithWork limits s
            first second tail he prepared.1
            (BinaryPRGHeapResourceLoop.pairWithWork_value
              (hC := hC) limits s first second tail he) branch
          let next := selected.1
          have hSelected := budget.selected s first second tail he branch hInvariant
          have hClosed := budget.closed s first second tail he branch hInvariant
          have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress
            limits s first second tail he prepared.1
            (BinaryPRGHeapResourceLoop.pairWithWork_value
              (hC := hC) limits s first second tail he) branch
          change selected.2 ≤ M at hSelected
          change Inv next at hClosed
          change next.active.length < s.active.length at hProgress
          have hFuel : next.active.length < fuel := hProgress.trans_le hSize
          have hLater := ih next.active.length hFuel next coin.1.2
            (BinaryWordIndexCoinController.sample_position_bounds
              seed prepared.1.probability q hq).2 hClosed le_rfl
          have hOne : next.active.length + 1 ≤ fuel := by omega
          have hMul := Nat.mul_le_mul_right (2 * M) hOne
          rw [Nat.add_mul,one_mul] at hMul
          change prepared.2 + coin.2 + selected.2 +
            (BinaryPRGHeapResourceLoop.runWithWork seed limits hC next coin.1.2
              (BinaryWordIndexCoinController.sample_position_bounds
                seed prepared.1.probability q hq).2).2 + 8 ≤
            fuel * (2 * M) + 2
          omega
      · omega

theorem runWithWork_inputCount_bound (seed : BinarySeedLookupTree.Store)
    (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ)
    (budget : ReachableStepBudget seed limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 ≤
      n * (2 * M) + 2 :=
  (runWithWork_bound seed limits hC Inv M budget state hInv pc hp).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (2 * M) state.active_length_le) 2)

theorem runWithWork_invariant (seed : BinarySeedLookupTree.Store)
    (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ)
    (budget : ReachableStepBudget seed limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (result : Finished capacity n hCount)
    (hSome : (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).1.1 = some result) :
    Inv result := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount)
      (q : FixedBinaryWord seed.width) (hq : q.value ≤ seed.cap.value),
      Inv s → s.active.length ≤ fuel →
      (BinaryPRGHeapResourceLoop.runWithWork seed limits hC s q hq).1.1 = some result →
      Inv result from h state.active.length state pc hp hInv le_rfl hSome
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s q hq hs hSize hResult
      unfold BinaryPRGHeapResourceLoop.runWithWork at hResult
      split at hResult
      · rename_i first second tail he
        dsimp only at hResult
        split at hResult
        · cases hResult
        · rename_i _ branch hCoin
          let prepared := BinaryPRGHeapResourceLoop.pairWithWork
            (hC := hC) limits s first second tail he
          let coin := BinaryWordIndexCoinController.sample seed prepared.1.probability q hq
          let selected := BinaryPRGHeapResourceLoop.selectWithWork limits s
            first second tail he prepared.1
            (BinaryPRGHeapResourceLoop.pairWithWork_value
              (hC := hC) limits s first second tail he) branch
          have hClosed := budget.closed s first second tail he branch hs
          have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress limits s
            first second tail he prepared.1
            (BinaryPRGHeapResourceLoop.pairWithWork_value
              (hC := hC) limits s first second tail he) branch
          change selected.1.active.length < s.active.length at hProgress
          exact ih selected.1.active.length (hProgress.trans_le hSize)
            selected.1 coin.1.2
            (BinaryWordIndexCoinController.sample_position_bounds
              seed prepared.1.probability q hq).2 hClosed le_rfl hResult
      · change some s = some result at hResult
        cases hResult
        exact hs

end Blotto.BinaryPRGHeapResourceLoopBudget
