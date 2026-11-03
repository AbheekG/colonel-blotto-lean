import Blotto.BinaryPRGHeapLoopLifetime

/-! Invariant-indexed retained allocation for the actual physical loop trace.
Final source contracts must instantiate these step premises from the original
lattice or reflected-height invariants and decreasing heap reservation. -/

namespace Blotto.BinaryPRGHeapLoopLifetimeBudget
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage BinaryPRGHeapPairLifetime BinaryPRGHeapLoopLifetime
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

structure ReachableBudget (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) : Prop where
  pairCoin : ∀ (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),Inv state →
    let prepared := pairWithTrace (hC := hC) limits state first second tail he
    usage prepared.2 + usage (BinaryWordCoinLifetime.sampleWithTrace seed prepared.1.probability pc hp).2 ≤ M
  selected : ∀ (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool),Inv state → usage (selectWithTrace limits state first second tail he outputs hOutputs branch).2 ≤ M
  closed : ∀ (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool),Inv state → Inv (selectWithTrace limits state first second tail he outputs hOutputs branch).1

theorem runWithTrace_usage (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) (budget : ReachableBudget seed limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (runWithTrace seed limits hC state pc hp).2 ≤ state.active.length * (2 * M + 64) + 32 := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount)
      (q : FixedBinaryWord seed.width) (hq : q.value ≤ seed.cap.value),
      Inv s → s.active.length ≤ fuel → usage (runWithTrace seed limits hC s q hq).2 ≤ fuel * (2 * M + 64) + 32 from
    h state.active.length state pc hp hInv le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s q hq hs hSize
      conv_lhs => unfold BinaryPRGHeapLoopLifetime.runWithTrace
      split
      · rename_i first second tail he
        let prepared := pairWithTrace (hC := hC) limits s first second tail he
        let coin := BinaryWordCoinLifetime.sampleWithTrace seed prepared.1.probability q hq
        have hPair := budget.pairCoin s first second tail he q hq hs
        change usage prepared.2 + usage coin.2 ≤ M at hPair
        dsimp only
        split
        · have hw := wrap_usage 24 2 [prepared.2,coin.2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          have hPositive : 1 ≤ fuel := by
            have hTwo : 2 ≤ s.active.length := by rw [he]; simp
            omega
          have hm := Nat.mul_le_mul_right (2 * M + 64) hPositive
          change usage (wrap 24 2 [prepared.2,coin.2]) ≤ _
          omega
        · rename_i _ branch hCoin
          have hOutputs : prepared.1 = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) s first second tail he).outputs :=
            (pairWithTrace_erasure limits s first second tail he).trans
              (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he)
          let selected := selectWithTrace limits s first second tail he prepared.1 hOutputs branch
          have hSelected := budget.selected s first second tail he prepared.1 hOutputs branch hs
          have hClosed := budget.closed s first second tail he prepared.1 hOutputs branch hs
          have hProgress := selectWithTrace_progress limits s first second tail he prepared.1 hOutputs branch
          change usage selected.2 ≤ M at hSelected
          change Inv selected.1 at hClosed
          change selected.1.active.length < s.active.length at hProgress
          have hLater := ih selected.1.active.length (hProgress.trans_le hSize) selected.1 coin.1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position seed prepared.1.probability q hq).2 hClosed le_rfl
          let later := runWithTrace seed limits hC selected.1 coin.1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position seed prepared.1.probability q hq).2
          change usage later.2 ≤ selected.1.active.length * (2 * M + 64) + 32 at hLater
          have hw := wrap_usage 32 2 [prepared.2,coin.2,selected.2,later.2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          have hOne : selected.1.active.length + 1 ≤ fuel := by omega
          have hm := Nat.mul_le_mul_right (2 * M + 64) hOne
          rw [Nat.add_mul,one_mul] at hm
          change usage (wrap 32 2 [prepared.2,coin.2,selected.2,later.2]) ≤ _
          omega
      · have hw := wrap_usage 16 2 []
        simp only [List.map_nil,List.sum_nil] at hw
        change usage (wrap 16 2 []) ≤ _
        omega

theorem run_all_prefix (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) (budget : ReachableBudget seed limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace seed limits hC state pc hp).2 steps ≤ borrowed + n * (2 * M + 64) + 32 ∧
      framePeak ((runWithTrace seed limits hC state pc hp).2.take steps) ≤ n * (2 * M + 64) + 32 := by
  have h := (runWithTrace_usage seed limits hC Inv M budget state hInv pc hp).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (2 * M + 64) state.active_length_le) 32)
  have hpref := all_prefix _ _ h borrowed steps
  exact ⟨by omega,hpref.2⟩

end Blotto.BinaryPRGHeapLoopLifetimeBudget
