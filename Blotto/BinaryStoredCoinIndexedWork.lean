import Blotto.BinaryStoredCoinIndexed
import Blotto.BinaryCoinWordWork

/-! Actual stored root coins retain their indexed Boolean path and residual
words. Primitive word work and padding derive from the original stored width;
reader/index representation, physical allocation and full controllers remain
separate. No positivity/unit promise is needed for the generic work envelope. -/

namespace Blotto.BinaryStoredCoinIndexedWork
open BinaryRationalNormalization

def runWithWork {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (a b : FixedBinaryWord w)
    (pos : ℕ) (_hp : pos ≤ N) : (Option Bool × ℕ) × ℕ :=
  let body := FixedWordCoin.bodyWork a b + 2
  if a.isZero then ((some false,pos),body) else if a.same b then ((some true,pos),body) else
    if hRead : pos < N then
      let next := a.coinStep b
      if bits ⟨pos,hRead⟩ = next.1 then
        let later := runWithWork N bits next.2 b (pos + 1) (by omega)
        (later.1,body + later.2)
      else ((some (!bits ⟨pos,hRead⟩),pos + 1),body)
    else ((none,pos),body)
termination_by N - pos

theorem runWithWork_state {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (a b : FixedBinaryWord w)
    (pos : ℕ) (hp : pos ≤ N) :
    (runWithWork N bits a b pos hp).1 = BinaryStoredCoinIndexed.run N bits a b pos hp := by
  conv_lhs => unfold runWithWork
  conv_rhs => unfold BinaryStoredCoinIndexed.run
  dsimp only
  split_ifs
  · rfl
  · rfl
  · exact runWithWork_state N bits (a.coinStep b).2 b (pos + 1) (by omega)
  · rfl
  · rfl
termination_by N - pos

theorem runWithWork_bound {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (a b : FixedBinaryWord w)
    (pos : ℕ) (hp : pos ≤ N) : (runWithWork N bits a b pos hp).2 ≤ (24 * w + 30) * (N - pos + 1) := by
  have hBody := FixedWordCoin.bodyWork_bound a b
  rw [FixedWordCoin.bodyAllowance_eq] at hBody
  have hOne : 1 ≤ N - pos + 1 := by omega
  conv_lhs => unfold runWithWork
  dsimp only
  split_ifs
  · nlinarith
  · nlinarith
  · have hLater := runWithWork_bound N bits (a.coinStep b).2 b (pos + 1) (by omega)
    have hDepth : N - pos + 1 = (N - (pos + 1) + 1) + 1 := by omega
    rw [hDepth]
    nlinarith
  · nlinarith
  · nlinarith
termination_by N - pos

def sampleWithWork (word : SignedWord) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option Bool × ℕ) × ℕ :=
  let words := BinaryStoredRationalCoin.fromStored word.numerator word.denominator
  let result := runWithWork N bits words.1 words.2 pos hp
  (result.1,12 * (max word.numerator.length word.denominator.length + 1) + result.2)

theorem sampleWithWork_state (word : SignedWord) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (sampleWithWork word N bits pos hp).1 = BinaryStoredCoinIndexed.sample word N bits pos hp := by
  unfold sampleWithWork BinaryStoredCoinIndexed.sample
  exact runWithWork_state N bits _ _ pos hp

def bound (W remaining : ℕ) : ℕ := 12 * (W + 1) + (24 * W + 30) * (remaining + 1)

theorem sampleWithWork_bound (word : SignedWord) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N)
    (W : ℕ) (hW : width word ≤ W) : (sampleWithWork word N bits pos hp).2 ≤ bound W (N - pos) := by
  have h := runWithWork_bound N bits
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).1
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).2 pos hp
  unfold sampleWithWork bound BinaryStoredRationalCoin.fromStored
  dsimp only at *
  unfold width at hW
  exact Nat.add_le_add (Nat.mul_le_mul_left 12 (Nat.add_le_add_right hW 1))
    (h.trans (Nat.mul_le_mul_right _ (by omega)))

end Blotto.BinaryStoredCoinIndexedWork
