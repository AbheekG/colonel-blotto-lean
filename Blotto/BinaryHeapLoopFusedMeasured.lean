import Blotto.BinaryHeapPairSourceMeasured
import Blotto.BinaryHeapUpdateMeasured
import Blotto.BinaryWordCoinSourceMeasured
import Blotto.BinaryPRGHeapLoopMeasuredWork

/-! A single actual resource-loop recursion returns its result, old trace and
source charge. Pair reads/register execution and coins are fused producers.
The selected physical update also uses one fused producer. Actual write-address
reversal work is retained by selectMeasured; native execution costs remain open. -/
namespace Blotto.BinaryHeapLoopFusedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished Result)
open BinaryPRGHeapTraceUsage BinaryPRGHeapLoopLifetime
set_option autoImplicit false
set_option maxHeartbeats 500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

structure Prepared
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) where
  outputs : BinaryPRGWordControllerPairOutputs.Outputs
  trace : Trace
  work : ℕ
  valid : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs

set_option maxHeartbeats 300000 in
def prepare (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : Prepared hC state first second tail he :=
  let produced := BinaryHeapPairSourceMeasured.pair (hC := hC) limits state first second tail he
  ⟨produced.1.1,produced.1.2,produced.2,
    BinaryHeapPairSourceMeasured.pair_value (hC := hC) limits state first second tail he⟩

structure Draw (seed : BinarySeedLookupTree.Store) where
  outcome : Option Bool
  cursor : FixedBinaryWord seed.width
  trace : Trace
  work : ℕ
  bounded : cursor.value ≤ seed.cap.value

set_option maxHeartbeats 300000 in
def draw (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : Draw seed :=
  let produced := BinaryWordCoinSourceMeasured.sample seed word pc hp
  ⟨produced.1.1.1,produced.1.1.2,produced.1.2,produced.2,
    (BinaryWordCoinSourceMeasured.sample_position seed word pc hp).2⟩

structure Selection (state : Finished capacity n hCount) where
  value : Finished capacity n hCount
  trace : Trace
  work : ℕ
  decreases : value.active.length < state.active.length

set_option maxHeartbeats 300000 in
def selectReference (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : Selection state :=
  let selected := selectWithTrace (hC := hC) limits state first second tail he outputs hOutputs branch
  ⟨selected.1,selected.2,
    (BinaryPRGHeapResourceLoop.selectWithWork (hC := hC) limits state first second tail he outputs hOutputs branch).2,
    selectWithTrace_progress (hC := hC) limits state first second tail he outputs hOutputs branch⟩


def selectMeasured (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : Selection state × ℕ :=
  let produced := BinaryHeapUpdateMeasured.select (hC := hC) limits state first second tail he outputs hOutputs branch
  (⟨produced.1.1,produced.1.2,produced.2.1,
    BinaryHeapUpdateMeasured.select_progress (hC := hC) limits state first second tail he outputs hOutputs branch⟩,
    produced.2.2)

def select (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : Selection state :=
  (selectMeasured limits hC state first second tail he outputs hOutputs branch).1

theorem select_eq_reference (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    select limits hC state first second tail he outputs hOutputs branch =
      selectReference limits hC state first second tail he outputs hOutputs branch := by
  simp only [select,selectMeasured,selectReference,BinaryHeapUpdateMeasured.select_erases,
    BinaryHeapUpdateMeasured.select_work]

theorem selectMeasured_reversals_le_work (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectMeasured limits hC state first second tail he outputs hOutputs branch).2 ≤
      (selectMeasured limits hC state first second tail he outputs hOutputs branch).1.work := by
  exact BinaryHeapUpdateMeasured.select_reversals_le_work (hC := hC) limits state first second tail he outputs hOutputs branch

theorem selectMeasured_write_overhead_le_work (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectMeasured limits hC state first second tail he outputs hOutputs branch).2+9 ≤
      (selectMeasured limits hC state first second tail he outputs hOutputs branch).1.work := by
  exact BinaryHeapUpdateMeasured.select_write_overhead_le_work (hC := hC) limits state first second tail he outputs hOutputs branch

theorem select_trace (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    ((select limits hC state first second tail he outputs hOutputs branch).value,
      (select limits hC state first second tail he outputs hOutputs branch).trace) =
      selectWithTrace (hC := hC) limits state first second tail he outputs hOutputs branch := by
  rw [select_eq_reference]
  rfl

set_option maxHeartbeats 300000 in
/-- The initial active list is a structural ruler, consumed once per strict
active-list decrease. Its empty branch is unreachable while a pair remains,
as proved by the complete erasure/work theorems below. -/
def loop (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)) :
    List (Address capacity.width capacity.cap) →
      (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → (Result seed capacity n hCount × Trace) × ℕ
  | [],state,pc,_hp => (((some state,pc),wrap 16 2 []),2)
  | _::fuel,state,pc,hp =>
      match he : state.active with
      | first :: second :: tail =>
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.outputs.probability pc hp
          match coin.outcome with
          | none => (((none,coin.cursor),wrap 24 2 [prepared.trace,coin.trace]),prepared.work+coin.work+4)
          | some branch =>
              let selected := select limits hC state first second tail he prepared.outputs prepared.valid branch
              let later := loop seed limits hC fuel selected.value coin.cursor
                coin.bounded
              ((later.1.1,wrap 32 2 [prepared.trace,coin.trace,selected.trace,later.1.2]),
                prepared.work+coin.work+selected.work+later.2+8)
      | _ => (((some state,pc),wrap 16 2 []),2)
termination_by structural fuel _state _pc _hp => fuel

def run (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (Result seed capacity n hCount × Trace) × ℕ :=
  loop seed limits hC state.active state pc hp

set_option backward.isDefEq.respectTransparency true in
theorem loop_erases (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (hFuel : state.active.length ≤ fuel.length) :
    (loop seed limits hC fuel state pc hp).1 = BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp := by
  induction fuel generalizing state pc with
  | nil =>
      have he : state.active = [] := List.length_eq_zero_iff.mp (by simpa using hFuel)
      rw [loop,BinaryPRGHeapLoopLifetime.runWithTrace]
      split
      · rename_i first second tail hPair
        have hh := he.symm.trans hPair
        cases hh
      · rfl
  | cons marker fuel ih =>
      conv_lhs => unfold loop
      conv_rhs => unfold BinaryPRGHeapLoopLifetime.runWithTrace
      dsimp only
      split
      · rename_i first second tail he
        symm
        split
        · rename_i otherFirst otherSecond otherTail hOther
          have hHeads := List.cons.inj (he.symm.trans hOther)
          have hRest := List.cons.inj hHeads.2
          have hFirst := hHeads.1
          have hSecond := hRest.1
          have hTail := hRest.2
          subst otherFirst
          subst otherSecond
          subst otherTail
          symm
          simp only [prepare,draw,BinaryHeapPairSourceMeasured.pair_erases,BinaryWordCoinSourceMeasured.sample_erases,select_eq_reference,selectReference]
          split
          · rename_i hNone
            symm
            split
            · with_reducible rfl
            · rename_i other hOther
              with_reducible cases hNone.symm.trans hOther
          · rename_i branch hSome
            symm
            split
            · rename_i hNone
              with_reducible cases hSome.symm.trans hNone
            · rename_i otherBranch hOther
              have hBranch := by with_reducible exact Option.some.inj (hSome.symm.trans hOther)
              subst otherBranch
              symm
              have hOutputs := (BinaryPRGHeapPairLifetime.pairWithTrace_erasure (hC := hC) limits state first second tail he).trans
                (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he)
              have hProgress := selectWithTrace_progress (hC := hC) limits state first second tail he _ hOutputs branch
              have hLater := ih
                (selectWithTrace (hC := hC) limits state first second tail he _ hOutputs branch).1
                (BinaryWordCoinLifetime.sampleWithTrace seed
                  (BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC) limits state first second tail he).1.probability pc hp).1.2
                (BinaryWordCoinLifetime.sampleWithTrace_position seed _ pc hp).2 (by simp only [List.length_cons] at hFuel; omega)
              with_reducible exact congrArg (fun output : Result seed capacity n hCount × Trace =>
                (output.1,wrap 32 2 [
                  (BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC) limits state first second tail he).2,
                  (BinaryWordCoinLifetime.sampleWithTrace seed
                    (BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC) limits state first second tail he).1.probability pc hp).2,
                  (selectWithTrace (hC := hC) limits state first second tail he _ hOutputs branch).2,output.2])) hLater
        · rename_i hNoPair
          exact False.elim (hNoPair first second tail he)
      · rename_i hNoPair
        symm
        split
        · rename_i first second tail he
          exact False.elim (hNoPair first second tail he)
        · rfl

set_option backward.isDefEq.respectTransparency true in
theorem loop_work (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (hFuel : state.active.length ≤ fuel.length) :
    (loop seed limits hC fuel state pc hp).2 = (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 := by
  induction fuel generalizing state pc with
  | nil =>
      have he : state.active = [] := List.length_eq_zero_iff.mp (by simpa using hFuel)
      rw [loop,BinaryPRGHeapResourceLoop.runWithWork]
      split
      · rename_i first second tail hPair
        have hh := he.symm.trans hPair
        cases hh
      · rfl
  | cons marker fuel ih =>
      conv_lhs => unfold loop
      conv_rhs => unfold BinaryPRGHeapResourceLoop.runWithWork
      dsimp only
      split
      · rename_i first second tail he
        symm
        split
        · rename_i otherFirst otherSecond otherTail hOther
          have hHeads := List.cons.inj (he.symm.trans hOther)
          have hRest := List.cons.inj hHeads.2
          have hFirst := hHeads.1
          have hSecond := hRest.1
          have hTail := hRest.2
          subst otherFirst
          subst otherSecond
          subst otherTail
          symm
          simp only [prepare,draw,BinaryHeapPairSourceMeasured.pair_data,BinaryHeapPairSourceMeasured.pair_work,
            BinaryWordCoinSourceMeasured.sample_data,BinaryWordCoinSourceMeasured.sample_work,
            select_eq_reference,selectReference,selectWithTrace_erasure]
          split
          · rename_i hNone
            symm
            split
            · with_reducible rfl
            · rename_i other hOther
              with_reducible cases hNone.symm.trans hOther
          · rename_i branch hSome
            symm
            split
            · rename_i hNone
              with_reducible cases hSome.symm.trans hNone
            · rename_i otherBranch hOther
              have hBranch := by with_reducible exact Option.some.inj (hSome.symm.trans hOther)
              subst otherBranch
              symm
              have hOutputs := BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he
              have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress (hC := hC) limits state first second tail he _ hOutputs branch
              rw [ih _ _ _ (by simp only [List.length_cons] at hFuel; omega)]
        · rename_i hNoPair
          exact False.elim (hNoPair first second tail he)
      · rename_i hNoPair
        symm
        split
        · rename_i first second tail he
          exact False.elim (hNoPair first second tail he)
        · rfl

theorem run_erases (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed limits hC state pc hp).1 = BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp :=
  loop_erases seed limits hC state.active state pc hp le_rfl

theorem run_work (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed limits hC state pc hp).2 = (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 :=
  loop_work seed limits hC state.active state pc hp le_rfl

theorem run_eq_reference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    run seed limits hC state pc hp = BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork seed limits hC state pc hp := by
  apply Prod.ext
  · exact run_erases seed limits hC state pc hp
  · rw [run_work,BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork,BinaryPRGHeapLoopMeasuredWork.work_eq_source]

end Blotto.BinaryHeapLoopFusedMeasured
