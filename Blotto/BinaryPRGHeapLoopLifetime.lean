import Blotto.BinaryPRGHeapPairLifetime
import Blotto.BinaryPRGHeapUpdateLifetime
import Blotto.BinaryWordCoinLifetime

/-! The physical resource loop consumes traced pairs, shared-cap indexed
coins and selected physical updates. Exact erasure and an invariant-indexed
retained allocation bound cover success and exhaustion. -/

namespace Blotto.BinaryPRGHeapLoopLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished Result)
open BinaryPRGHeapTraceUsage BinaryPRGHeapPairLifetime
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def selectWithTrace (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : Finished capacity n hCount × Trace :=
  let chosen := if branch then outputs.upper else outputs.lower
  let selected := BinaryPRGHeapUpdateLifetime.updateWithTrace limits state first second tail chosen
  (⟨selected.1.1.ruler,selected.1.1.size,selected.1.1.heap,selected.1.1.root,
    selected.1.1.valid,selected.1.2,by
      rw [BinaryPRGHeapUpdateLifetime.updateWithTrace_erasure]
      exact (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he outputs hOutputs branch).1.certified⟩,
    wrap 16 2 [selected.2])

theorem selectWithTrace_erasure (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectWithTrace limits state first second tail he outputs hOutputs branch).1 =
      (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he outputs hOutputs branch).1 := by
  simp only [selectWithTrace,BinaryPRGHeapResourceLoop.selectWithWork,
    BinaryPRGHeapUpdateLifetime.updateWithTrace_erasure]

theorem selectWithTrace_progress (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectWithTrace limits state first second tail he outputs hOutputs branch).1.active.length < state.active.length := by
  rw [selectWithTrace_erasure]
  exact BinaryPRGHeapResourceLoop.selectWithWork_progress limits state first second tail he outputs hOutputs branch

theorem coin_erasure (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryWordCoinLifetime.sampleWithTrace seed word pc hp).1 =
      (BinaryWordIndexCoinController.sample seed word pc hp).1 :=
  (BinaryWordCoinLifetime.sampleWithTrace_erases seed word pc hp).trans
    (BinaryPRGWordControllerDataCoin.sample_erasure seed word pc hp).symm

def runWithTrace (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Result seed capacity n hCount × Trace :=
  match he : state.active with
  | first :: second :: tail =>
      let prepared := pairWithTrace (hC := hC) limits state first second tail he
      let coin := BinaryWordCoinLifetime.sampleWithTrace seed prepared.1.probability pc hp
      match coin.1.1 with
      | none => ((none,coin.1.2),wrap 24 2 [prepared.2,coin.2])
      | some branch =>
          have hOutputs : prepared.1 = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs :=
            (pairWithTrace_erasure limits state first second tail he).trans
              (BinaryPRGHeapResourceLoop.pairWithWork_value limits state first second tail he)
          let selected := selectWithTrace limits state first second tail he prepared.1 hOutputs branch
          let later := runWithTrace seed limits hC selected.1 coin.1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position seed prepared.1.probability pc hp).2
          (later.1,wrap 32 2 [prepared.2,coin.2,selected.2,later.2])
  | _ => ((some state,pc),wrap 16 2 [])
termination_by state.active.length
decreasing_by exact selectWithTrace_progress limits state first second tail he prepared.1 _ branch

theorem runWithTrace_erasure (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runWithTrace seed limits hC state pc hp).1 =
      (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).1 := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount)
      (q : FixedBinaryWord seed.width) (hq : q.value ≤ seed.cap.value),s.active.length ≤ fuel →
      (runWithTrace seed limits hC s q hq).1 =
        (BinaryPRGHeapResourceLoop.runWithWork seed limits hC s q hq).1 from
    h state.active.length state pc hp le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s q hq hSize
      conv_lhs => unfold runWithTrace
      conv_rhs => unfold BinaryPRGHeapResourceLoop.runWithWork
      split
      · rename_i first second tail he
        split
        · rename_i otherFirst otherSecond otherTail hOther
          have hHeads := List.cons.inj (he.symm.trans hOther)
          have hRest := List.cons.inj hHeads.2
          have hFirst : first = otherFirst := hHeads.1
          have hSecond : second = otherSecond := hRest.1
          have hTail : tail = otherTail := hRest.2
          subst otherFirst
          subst otherSecond
          subst otherTail
          simp only [pairWithTrace_erasure,coin_erasure]
          cases hc : (BinaryWordIndexCoinController.sample seed
            (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits s first second tail he).1.probability q hq).1.1 with
          | none => rfl
          | some branch =>
              simp only [selectWithTrace_erasure]
              let selected := BinaryPRGHeapResourceLoop.selectWithWork limits s first second tail he
                (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits s first second tail he).1
                (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he) branch
              have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress limits s first second tail he
                (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits s first second tail he).1
                (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he) branch
              exact ih selected.1.active.length (hProgress.trans_le hSize) selected.1
                (BinaryWordIndexCoinController.sample seed
                  (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits s first second tail he).1.probability q hq).1.2
                (BinaryWordIndexCoinController.sample_position_bounds seed _ q hq).2 le_rfl
        · rename_i hNoPair
          exact False.elim (hNoPair first second tail he)
      · rename_i hNoPair
        split
        · rename_i first second tail he
          exact False.elim (hNoPair first second tail he)
        · rfl

end Blotto.BinaryPRGHeapLoopLifetime
