import Blotto.FixedBinaryWord
import Blotto.BinarySignedMagnitude
import Blotto.BinaryRationalOpcode

/-! A bounded rational coin consumes already stored Boolean numerator and
denominator words. Padding depends only on list lengths, and the pending loop
uses Boolean zero/equality scans and fixed-width subtract/drop steps. Numeric
values occur solely in the exact rational-coin refinement specification. -/

namespace Blotto.BinaryStoredRationalCoin
open BinaryRationalNormalization

def run {w : ℕ} : (K : ℕ) → FixedBinaryWord w → FixedBinaryWord w → (Fin K → Bool) → Option Bool × ℕ
  | 0,a,b,_ => if a.isZero then (some false,0) else if a.same b then (some true,0) else (none,0)
  | K+1,a,b,bits =>
      if a.isZero then (some false,0) else if a.same b then (some true,0) else
        let next:=a.coinStep b
        if bits 0=next.1 then
          let later:=run K next.2 b (Fin.tail bits)
          (later.1,later.2+1)
        else (some (!bits 0),1)

theorem run_refines {w : ℕ} (K : ℕ) (a b : FixedBinaryWord w) (_hb : 0<b.value) (hab : a.value≤b.value)
    (bits : Fin K→Bool) : run K a b bits = runFixedDenominatorCoin K a.value b.value bits := by
  induction K generalizing a with
  | zero =>
      have hSame : a.same b=true ↔ b.value≤a.value := by rw [a.same_value b]; omega
      simp only [run,runFixedDenominatorCoin,a.isZero_value,hSame]
  | succ K ih =>
      have hSame : a.same b=true ↔ b.value≤a.value := by rw [a.same_value b]; omega
      simp only [run,runFixedDenominatorCoin,a.isZero_value,hSame,FixedBinaryWord.coinStep_digit]
      split_ifs with hz he hd
      · rfl
      · rfl
      · have hlt : a.value<b.value := by omega
        have hr := ih (a.coinStep b).2 (a.coinStep_normalized b hlt).le (Fin.tail bits)
        rw [FixedBinaryWord.coinStep_residual a b hlt] at hr
        rw [hr]
      · rfl

def fromStored (numerator denominator : List Bool) :
    FixedBinaryWord (max numerator.length denominator.length) × FixedBinaryWord (max numerator.length denominator.length) :=
  (⟨BinarySignedMagnitude.pad _ numerator,BinarySignedMagnitude.pad_length _ numerator (Nat.le_max_left _ _)⟩,
    ⟨BinarySignedMagnitude.pad _ denominator,BinarySignedMagnitude.pad_length _ denominator (Nat.le_max_right _ _)⟩)

theorem fromStored_values (numerator denominator : List Bool) :
    (fromStored numerator denominator).1.value=BinaryBigEndian.littleValue numerator ∧
      (fromStored numerator denominator).2.value=BinaryBigEndian.littleValue denominator :=
  ⟨BinarySignedMagnitude.pad_value _ _,BinarySignedMagnitude.pad_value _ _⟩

def sample (word : SignedWord) (K : ℕ) (bits : Fin K→Bool) : Option Bool×ℕ :=
  let words:=fromStored word.numerator word.denominator
  run K words.1 words.2 bits

theorem sample_refines (word : SignedWord) (hValid : BinaryRationalOpcode.Valid word)
    (hSign : word.negative=false) (hUnit : BinaryBigEndian.littleValue word.numerator≤BinaryBigEndian.littleValue word.denominator)
    (K : ℕ) (bits : Fin K→Bool) : sample word K bits=runRationalCoin K (value word) bits := by
  have hValues:=fromStored_values word.numerator word.denominator
  unfold sample
  rw [run_refines K _ _ (by rw [hValues.2]; exact hValid) (by rw [hValues.1,hValues.2]; exact hUnit),
    hValues.1,hValues.2,runFixedDenominatorCoin_refines K _ _ hValid]
  unfold value
  rw [hSign]
  rfl

theorem sample_bits_le (word : SignedWord) (hValid : BinaryRationalOpcode.Valid word)
    (hSign : word.negative=false) (hUnit : BinaryBigEndian.littleValue word.numerator≤BinaryBigEndian.littleValue word.denominator)
    (K : ℕ) (bits : Fin K→Bool) : (sample word K bits).2≤K := by
  rw [sample_refines word hValid hSign hUnit K bits]
  exact runRationalCoin_bits_le _ _ _

end Blotto.BinaryStoredRationalCoin
