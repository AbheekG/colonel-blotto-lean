import Blotto.GeneralPaperStoredBasePrice

/-! Arithmetic-only shared-square table builder for the real-RAM model.
The bounded arithmetic quotient is used once per square; the resulting
number/work record is reused. Integer division is not a real-RAM primitive.
Both arithmetic and bit builders return the same complete native table.
-/
namespace Blotto.GeneralPaperPowerTableArithmetic
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (unit p : ℕ) (base : Number) : ℕ → Table × ℕ
  | 0 => (⟨[],⟨1,base⟩,2⟩,16)
  | columns+1 =>
    let earlier := run unit p base columns
    if columns=0 then
      (⟨⟨1,base⟩::earlier.1.entries,⟨1,base⟩,earlier.1.work+8⟩,earlier.2+64)
    else
      let product := GeneralPaperDyadicMultiply.multiply unit p earlier.1.top.number earlier.1.top.number
      let next : Entry := ⟨2*earlier.1.top.degree,product.number⟩
      (⟨next::earlier.1.entries,next,earlier.1.work+product.work+16⟩,earlier.2+product.work+128)

theorem data (unit p columns : ℕ) (base : Number) : (run unit p base columns).1=build unit p base columns := by
  induction columns with
  | zero => rfl
  | succ columns ih =>
    rw [run,build]
    dsimp only
    rw [ih]
    split
    · rfl
    · simp only [square,Nat.add_assoc]

theorem work (unit p columns : ℕ) (base : Number) :
    (run unit p base columns).2≤columns*(12*(p+1)+194)+16 := by
  induction columns with
  | zero => simp only [run,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ columns ih =>
    rw [run]
    dsimp only
    split
    · nlinarith only [ih]
    · have hp := GeneralPaperDyadicMultiply.multiply_work unit p (run unit p base columns).1.top.number
        (run unit p base columns).1.top.number
      dsimp only
      nlinarith only [ih,hp]

end Blotto.GeneralPaperPowerTableArithmetic
