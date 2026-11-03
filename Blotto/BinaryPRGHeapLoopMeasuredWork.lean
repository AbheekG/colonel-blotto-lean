import Blotto.BinaryPRGHeapLoopLifetime

/-! The selected physical loop carries the same exact source-work recurrence as
the resource worker, alongside its retained-storage trace. -/
namespace Blotto.BinaryPRGHeapLoopMeasuredWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished Result)
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def work (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) : ℕ :=
  match he : state.active with
  | first :: second :: tail =>
      let prepared := BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC)
        limits state first second tail he
      let pairCharge := (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
        limits state first second tail he).2
      let coin := BinaryWordCoinLifetime.sampleWithTrace seed prepared.1.probability pc hp
      let coinCharge := (BinaryWordIndexCoinController.sample
        seed prepared.1.probability pc hp).2
      match coin.1.1 with
      | none => pairCharge + coinCharge + 4
      | some branch =>
          have hOutputs : prepared.1 =
              (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC)
                state first second tail he).outputs :=
            (BinaryPRGHeapPairLifetime.pairWithTrace_erasure limits state first second tail he).trans
              (BinaryPRGHeapResourceLoop.pairWithWork_value limits state first second tail he)
          let selected := BinaryPRGHeapLoopLifetime.selectWithTrace limits state
            first second tail he prepared.1 hOutputs branch
          let selectedCharge := (BinaryPRGHeapResourceLoop.selectWithWork limits state
            first second tail he prepared.1 hOutputs branch).2
          pairCharge + coinCharge + selectedCharge +
            work seed limits hC selected.1 coin.1.2
              (BinaryWordCoinLifetime.sampleWithTrace_position seed prepared.1.probability pc hp).2 + 8
  | _ => 2
termination_by state.active.length
decreasing_by
  exact BinaryPRGHeapLoopLifetime.selectWithTrace_progress limits state
    first second tail he prepared.1 _ branch

def runWithTraceAndWork (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) :
    (Result seed capacity n hCount × Trace) × ℕ :=
  (BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp,
    work seed limits hC state pc hp)

theorem runWithTraceAndWork_erases (seed : BinarySeedLookupTree.Store)
    (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) :
    (runWithTraceAndWork seed limits hC state pc hp).1 =
      BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp := rfl

theorem work_eq_source (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) :
    work seed limits hC state pc hp =
      (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount)
      (q : FixedBinaryWord seed.width) (hq : q.value ≤ seed.cap.value),
      s.active.length ≤ fuel →
      work seed limits hC s q hq =
        (BinaryPRGHeapResourceLoop.runWithWork seed limits hC s q hq).2 from
    h state.active.length state pc hp le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s q hq hSize
      conv_lhs => unfold work
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
          simp only [BinaryPRGHeapPairLifetime.pairWithTrace_erasure,
            BinaryPRGHeapLoopLifetime.coin_erasure]
          cases hc : (BinaryWordIndexCoinController.sample seed
            (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
              limits s first second tail he).1.probability q hq).1.1 with
          | none => rfl
          | some branch =>
              simp only [BinaryPRGHeapLoopLifetime.selectWithTrace_erasure]
              let selected := BinaryPRGHeapResourceLoop.selectWithWork limits s
                first second tail he
                (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
                  limits s first second tail he).1
                (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he) branch
              have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress limits s
                first second tail he
                (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
                  limits s first second tail he).1
                (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he) branch
              have hLater := ih selected.1.active.length (hProgress.trans_le hSize)
                selected.1
                (BinaryWordIndexCoinController.sample seed
                  (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
                    limits s first second tail he).1.probability q hq).1.2
                (BinaryWordIndexCoinController.sample_position_bounds seed _ q hq).2 le_rfl
              simpa only [selected] using congrArg
                (fun value => (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
                    limits s first second tail he).2 +
                  (BinaryWordIndexCoinController.sample seed
                    (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
                      limits s first second tail he).1.probability q hq).2 +
                  selected.2 + value + 8) hLater
        · rename_i hNoPair
          exact False.elim (hNoPair first second tail he)
      · rename_i hNoPair
        split
        · rename_i first second tail he
          exact False.elim (hNoPair first second tail he)
        · rfl

theorem runWithTraceAndWork_charge (seed : BinarySeedLookupTree.Store)
    (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) :
    (runWithTraceAndWork seed limits hC state pc hp).2 =
      (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 :=
  work_eq_source seed limits hC state pc hp

end Blotto.BinaryPRGHeapLoopMeasuredWork
