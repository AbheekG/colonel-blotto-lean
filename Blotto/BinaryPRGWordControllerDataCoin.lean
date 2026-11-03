import Blotto.BinaryWordIndexCoinController
import Blotto.BinaryPRGWordControllerCoinConsumption

/-! Explicit data-only Boolean program-counter coin execution. No work,
visited-cell, length/count or numeric index observer executes in this loop.
The universal erasure equality connects it to the derived joined ledger;
physical pointer/layout/allocator and full caller machine claims are separate. -/

namespace Blotto.BinaryPRGWordControllerDataCoin
open BinarySeedLookupTree

abbrev Result (store : Store) := Option Bool × FixedBinaryWord store.width

/-- The actual coin path stores only Boolean words and Boolean control tags. -/
def run {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) : Result store :=
  if a.isZero then (some false,pc) else if a.same b then (some true,pc) else
    if hRead : BinaryIndexWord.lt pc store.cap = true then
      let bit := store.lookup pc
      let next := a.coinStep b
      let advanced := BinaryIndexWord.increment pc
      if bit = next.1 then
        run store next.2 b advanced.1 (BinaryWordIndexCoinController.advance_bound store pc hRead)
      else (some (!bit),advanced.1)
    else (none,pc)
termination_by store.cap.value - pc.value
decreasing_by
  have hr := (BinaryWordIndexCoinController.guard_value store pc).mp hRead
  have hn := BinaryWordIndexCoinController.advance_value store pc hRead
  change (BinaryIndexWord.increment pc).1.value = pc.value + 1 at hn
  omega

theorem run_erasure {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordIndexCoinController.run store a b pc hp).1 = run store a b pc hp := by
  conv_lhs => unfold BinaryWordIndexCoinController.run
  conv_rhs => unfold run
  dsimp only [Store.lookupWithVisits,BinaryIndexWord.ltWithWork,BinaryIndexWord.incrementWithWork]
  split_ifs with hz he hRead hd
  · rfl
  · rfl
  · exact run_erasure store (a.coinStep b).2 b (BinaryIndexWord.increment pc).1
      (BinaryWordIndexCoinController.advance_bound store pc hRead)
  · rfl
  · rfl
termination_by store.cap.value - pc.value
decreasing_by
  have hr := (BinaryWordIndexCoinController.guard_value store pc).mp hRead
  have hn := BinaryWordIndexCoinController.advance_value store pc hRead
  change (BinaryIndexWord.increment pc).1.value = pc.value + 1 at hn
  omega

def sample (store : Store) (word : BinaryRationalNormalization.SignedWord)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  let words := BinaryStoredRationalCoin.fromStored word.numerator word.denominator
  run store words.1 words.2 pc hp

theorem sample_erasure (store : Store) (word : BinaryRationalNormalization.SignedWord)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordIndexCoinController.sample store word pc hp).1 = sample store word pc hp := by
  unfold BinaryWordIndexCoinController.sample sample
  exact run_erasure store _ _ pc hp

theorem sample_position (store : Store) (word : BinaryRationalNormalization.SignedWord)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (sample store word pc hp).2.value ∧ (sample store word pc hp).2.value ≤ store.cap.value := by
  rw [← sample_erasure]
  exact BinaryWordIndexCoinController.sample_position_bounds store word pc hp

theorem sample_contract (store : Store) (word : BinaryRationalNormalization.SignedWord)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((sample store word pc hp).1,(sample store word pc hp).2.value) =
      BinaryStoredCoinIndexed.sample word store.cap.value (BinaryWordIndexCoinController.reader store) pc.value hp ∧
      (BinaryWordIndexCoinController.sample store word pc hp).2 ≤
        12 * (BinaryRationalNormalization.width word + 1) +
          BinaryWordIndexCoinController.allowance (BinaryRationalNormalization.width word) store.width *
            ((sample store word pc hp).2.value - pc.value + 1) := by
  constructor
  · rw [← sample_erasure]
    exact BinaryWordIndexCoinController.sample_state store word pc hp
  · rw [← sample_erasure]
    exact BinaryPRGWordControllerCoinConsumption.sample_bound store word pc hp

end Blotto.BinaryPRGWordControllerDataCoin
