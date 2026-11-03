import Blotto.FixedWordCoinRefinement

/-! Explicit primitive Boolean/traversal allowances for one coin-word step.
These cover subtraction, padding, output spines and high-bit removal. Numeric
encoding, reader/index arithmetic, physical allocation and whole-controller
integration remain separate costs. -/

namespace Blotto.BinaryCoinWord

def chosenResidual (a b : List Bool) : List Bool :=
  let doubled := false :: a
  let result := BinaryBorrowWord.subtract doubled (b ++ [false]) false
  if result.2 then doubled else result.1

theorem chosenResidual_length (a b : List Bool) (h : a.length = b.length) :
    (chosenResidual a b).length = a.length + 1 := by
  have hs := BinaryBorrowWord.subtract_length (false :: a) (b ++ [false]) false (input_lengths a b h)
  unfold chosenResidual
  dsimp only
  split_ifs
  · rfl
  · simpa only [List.length_cons] using hs

-- Boolean difference/borrow uses at most eight primitive Boolean operations
-- per column. The remaining terms price reads, cons cells and loop visits.
def stepWork (a b : List Bool) : ℕ :=
  1 + (b.length + 1) + 8 * (a.length + 1) + 2 * (a.length + 1) +
    2 * (a.length + 1) + BinaryBorrowWord.visits (false :: a) (b ++ [false]) +
    BinaryWordHighBit.visits (chosenResidual a b) + 2 * a.length + 1

theorem stepWork_bound (a b : List Bool) (h : a.length = b.length) :
    stepWork a b ≤ 17 * a.length + 19 := by
  have hSub := BinaryBorrowWord.visits_eq (false :: a) (b ++ [false]) (input_lengths a b h)
  have hDrop := BinaryWordHighBit.visits_bound (chosenResidual a b)
  rw [chosenResidual_length a b h] at hDrop
  simp only [List.length_cons] at hSub
  unfold stepWork
  omega

end Blotto.BinaryCoinWord
namespace Blotto.FixedWordCoin

-- Three labels per zero-scan visit, four per equality-scan visit, plus two
-- outcome labels. Full word-step allowance is conservative at every visit.
def bodyAllowance (w : ℕ) : ℕ := 3 * (w + 1) + 4 * (w + 1) + (17 * w + 19) + 2

theorem bodyAllowance_eq (w : ℕ) : bodyAllowance w = 24 * w + 28 := by unfold bodyAllowance; omega

def bodyWork {w : ℕ} (a b : FixedBinaryWord w) : ℕ :=
  3 * FixedBinaryWord.zeroVisits a.bits + 4 * FixedBinaryWord.sameVisits a.bits b.bits +
    BinaryCoinWord.stepWork a.bits b.bits + 2

theorem bodyWork_bound {w : ℕ} (a b : FixedBinaryWord w) : bodyWork a b ≤ bodyAllowance w := by
  have hz := FixedBinaryWord.zeroVisits_bound a.bits
  have he := FixedBinaryWord.sameVisits_bound a.bits b.bits
  have hs := BinaryCoinWord.stepWork_bound a.bits b.bits (a.size.trans b.size.symm)
  rw [a.size] at hz he hs
  unfold bodyWork bodyAllowance
  omega

def visits {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (_hpos : pos ≤ N)
    (a b : FixedBinaryWord w) (hb : 0 < b.value) (hab : a.value ≤ b.value) : ℕ :=
  if hz : a.isZero = true then 1 else
    if he : a.same b = true then 1 else
      if hRead : pos < N then
        let next := a.coinStep b
        have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
        if bits ⟨pos, hRead⟩ = next.1 then
          1 + visits N bits (pos + 1) (by omega) next.2 b hb (a.coinStep_normalized b hlt).le
        else 1
      else 1
termination_by N - pos
decreasing_by omega

theorem visits_bound {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (a b : FixedBinaryWord w) (hb : 0 < b.value) (hab : a.value ≤ b.value) :
    visits N bits pos hpos a b hb hab ≤ N - pos + 1 := by
  unfold visits
  split_ifs with hz he hRead
  · omega
  · omega
  · dsimp only
    split_ifs
    · have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      have h := visits_bound N bits (pos + 1) (by omega) (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le
      omega
    · omega
  · omega
termination_by N - pos
decreasing_by omega

def wordWork {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (a b : FixedBinaryWord w)
    (hb : 0 < b.value) (hab : a.value ≤ b.value) : ℕ :=
  bodyAllowance w * visits N bits 0 (Nat.zero_le _) a b hb hab

theorem wordWork_bound {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (a b : FixedBinaryWord w)
    (hb : 0 < b.value) (hab : a.value ≤ b.value) :
    wordWork N bits a b hb hab ≤ (24 * w + 28) * (N + 1) := by
  unfold wordWork
  rw [bodyAllowance_eq]
  exact Nat.mul_le_mul_left _ (by simpa only [Nat.sub_zero] using visits_bound N bits 0 (Nat.zero_le _) a b hb hab)

end Blotto.FixedWordCoin
