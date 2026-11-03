import Blotto.BinaryWordIndexCoinController

/-! A consumption-sensitive source-derived bound for the concrete Boolean-PC
coin. The shared-cap join charges the actual reached counter span, so composing
several coins does not pay the whole remaining seed budget for each coin. -/

namespace Blotto.BinaryPRGWordControllerCoinConsumption
open BinarySeedLookupTree BinaryWordIndexCoinController

 theorem run_bound {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).2 ≤ allowance width store.width *
      ((run store a b pc hp).1.2.value - pc.value + 1) := by
  have hb := body_bound a b
  have hg := BinaryIndexWord.ltWithWork_bound pc store.cap
  have hl := local_bound store a b pc
  conv_lhs => unfold run
  conv_rhs => arg 2; arg 1; arg 1; unfold run
  dsimp only
  split_ifs with hz he hRead hd
  · simp only [Nat.sub_self,Nat.zero_add,Nat.mul_one]
    unfold allowance
    omega
  · simp only [Nat.sub_self,Nat.zero_add,Nat.mul_one]
    unfold allowance
    omega
  · have hn := advance_value store pc hRead
    have ih := run_bound store (a.coinStep b).2 b
      (BinaryIndexWord.incrementWithWork pc).1.1 (advance_bound store pc hRead)
    have hm := (run_position_bounds store (a.coinStep b).2 b
      (BinaryIndexWord.incrementWithWork pc).1.1 (advance_bound store pc hRead)).1
    have hSpan :
        (run store (a.coinStep b).2 b (BinaryIndexWord.incrementWithWork pc).1.1
          (advance_bound store pc hRead)).1.2.value - pc.value + 1 =
        ((run store (a.coinStep b).2 b (BinaryIndexWord.incrementWithWork pc).1.1
          (advance_bound store pc hRead)).1.2.value -
          (BinaryIndexWord.incrementWithWork pc).1.1.value + 1) + 1 := by omega
    rw [hSpan]
    nlinarith
  · rw [advance_value store pc hRead]
    have hs : pc.value + 1 - pc.value + 1 = 2 := by omega
    rw [hs]
    nlinarith
  · simp only [Nat.sub_self,Nat.zero_add,Nat.mul_one]
    unfold allowance
    omega
termination_by store.cap.value - pc.value
decreasing_by
  have hr := (guard_value store pc).mp hRead
  have _hn := advance_value store pc hRead
  omega

 theorem sample_bound (store : Store) (word : BinaryRationalNormalization.SignedWord)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (sample store word pc hp).2 ≤
      12 * (BinaryRationalNormalization.width word + 1) +
        allowance (BinaryRationalNormalization.width word) store.width *
          ((sample store word pc hp).1.2.value - pc.value + 1) := by
  unfold sample
  dsimp only
  exact Nat.add_le_add_left (run_bound store
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).1
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).2 pc hp) _

end Blotto.BinaryPRGWordControllerCoinConsumption
