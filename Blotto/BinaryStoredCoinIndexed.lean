import Blotto.BinaryStoredRationalCoin
import Blotto.BinarySharedResourceRun
import Blotto.WordMachineRunEmbedding
import Blotto.BinaryCategoricalPreparation

/-! A pending stored Boolean coin uses one caller reader and current index.
Every read increments that index; zero/one coins read none. The exact numeric
reference is a coin between two selected Bool states, not a new sampling cap. -/

namespace Blotto.BinaryStoredCoinIndexed
open BinaryRationalNormalization

def run {w : ℕ} (N : ℕ) (bits : Fin N→Bool) (a b : FixedBinaryWord w)
    (pos : ℕ) (_hpos : pos≤N) : Option Bool×ℕ:=
  if a.isZero then (some false,pos) else if a.same b then (some true,pos) else
    if hRead : pos<N then
      let next:=a.coinStep b
      if bits ⟨pos,hRead⟩=next.1 then run N bits next.2 b (pos+1) (by omega)
      else (some (!bits ⟨pos,hRead⟩),pos+1)
    else (none,pos)
termination_by N-pos

def selected : WordStateMachine Bool Bool where
  step:=WordTransition.done
  rank:=fun _=>0
  progress:=by intro s; trivial

theorem selected_run (N : ℕ) (bits : Fin N→Bool) (branch : Bool) (pos : ℕ) (hpos : pos≤N) :
    selected.runCursorIndexed N bits (.state branch) pos hpos=(some branch,pos):=by
  conv_lhs=>unfold WordStateMachine.runCursorIndexed
  rfl

theorem run_refines {w : ℕ} (N : ℕ) (bits : Fin N→Bool) (a b : FixedBinaryWord w)
    (hb : 0<b.value) (hab : a.value≤b.value) (pos : ℕ) (hpos : pos≤N) :
    run N bits a b pos hpos=selected.runCursorIndexed N bits (.coin a.value b.value hb hab true false) pos hpos:=by
  conv_lhs=>unfold run
  conv_rhs=>unfold WordStateMachine.runCursorIndexed
  have hSame : a.same b=true ↔ b.value≤a.value:=by rw [a.same_value b]; omega
  simp only [a.isZero_value,hSame]
  by_cases hz : a.value=0
  · simp only [hz,ite_true,selected_run]
  · simp only [hz,ite_false]
    by_cases he : b.value≤a.value
    · simp only [he,ite_true,selected_run]
    · simp only [he,ite_false]
      by_cases hRead : pos<N
      · simp only [dite_eq_left hRead,FixedBinaryWord.coinStep_digit]
        have hlt : a.value<b.value:=by omega
        by_cases hd : bits ⟨pos,hRead⟩=denominatorDigit a.value b.value
        · simp only [hd,ite_true]
          have ih:=run_refines N bits (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le (pos+1) (by omega)
          simpa only [FixedBinaryWord.coinStep_residual a b hlt] using ih
        · simp only [hd,ite_false]
          cases hBit : bits ⟨pos,hRead⟩ <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_true,ite_false,selected_run]
      · simp only [dite_eq_right hRead]
termination_by N-pos

-- A positive canonical rational has the retained numerator/denominator fields.
theorem word_numbers (word : SignedWord) (hValid : BinaryRationalOpcode.Valid word)
    (hCoprime : Nat.Coprime (BinaryBigEndian.littleValue word.numerator) (BinaryBigEndian.littleValue word.denominator))
    (hNonnegative : 0≤value word) (hUnit : value word≤1) :
    let p:=ProbabilityWords.ofRat (value word) ⟨hNonnegative,hUnit⟩
    BinaryBigEndian.littleValue word.numerator=p.numerator ∧ BinaryBigEndian.littleValue word.denominator=p.denominator:=by
  have he:=BinaryRationalOpcode.value_num_den_of_coprime word hValid hCoprime
  constructor
  · change _=(value word).num.toNat
    rw [←he.1]
    exact ProbabilityWords.nonnegative_abs_eq_toNat _ hNonnegative
  · exact he.2.symm

def sample (word : SignedWord) (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hpos : pos≤N) : Option Bool×ℕ:=
  let words:=BinaryStoredRationalCoin.fromStored word.numerator word.denominator
  run N bits words.1 words.2 pos hpos

theorem sample_refines (word : SignedWord) (hValid : BinaryRationalOpcode.Valid word)
    (hUnit : BinaryBigEndian.littleValue word.numerator≤BinaryBigEndian.littleValue word.denominator)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hpos : pos≤N) :
    sample word N bits pos hpos=selected.runCursorIndexed N bits
      (.coin (BinaryBigEndian.littleValue word.numerator) (BinaryBigEndian.littleValue word.denominator) hValid hUnit true false) pos hpos:=by
  have he:=BinaryStoredRationalCoin.fromStored_values word.numerator word.denominator
  unfold sample
  rw [run_refines N bits _ _ (by rw [he.2]; exact hValid) (by rw [he.1,he.2]; exact hUnit)]
  congr 1
  exact BinarySharedResourceRun.coin_eq _ _ _ _ _ _ _ _ _ _ he.1 he.2

theorem sample_position (word : SignedWord) (hValid : BinaryRationalOpcode.Valid word)
    (hUnit : BinaryBigEndian.littleValue word.numerator≤BinaryBigEndian.littleValue word.denominator)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hpos : pos≤N) :
    pos≤(sample word N bits pos hpos).2 ∧ (sample word N bits pos hpos).2≤N:=by
  rw [sample_refines word hValid hUnit]
  exact selected.runCursorIndexed_position_bounds _ _ _ _ _

end Blotto.BinaryStoredCoinIndexed
