import Blotto.GeneralPaperPowerQueryPrice

/-! Arithmetic-only query on the same retained columns. Chosen products
use the bounded arithmetic quotient, and each returned product is reused.
Its operation budget includes every branch, subtraction and native result.
-/
namespace Blotto.GeneralPaperPowerQueryArithmetic
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
set_option autoImplicit false
set_option maxHeartbeats 6000000

def scan (unit p : ℕ) : List Entry → ℕ → Number → GeneralPaperRoundedPowerQuery.Result × ℕ
  | [],remaining,acc => (⟨acc,remaining,2⟩,16)
  | entry::rest,remaining,acc =>
    if entry.degree≤remaining then
      let product := GeneralPaperDyadicMultiply.multiply unit p acc entry.number
      let later := scan unit p rest (remaining-entry.degree) product.number
      (⟨later.1.number,later.1.remaining,product.work+later.1.work+16⟩,product.work+later.2+128)
    else
      let later := scan unit p rest remaining acc
      (⟨later.1.number,later.1.remaining,later.1.work+8⟩,later.2+32)

theorem scan_data (unit p : ℕ) (entries : List Entry) (exponent : ℕ) (acc : Number) :
    (scan unit p entries exponent acc).1=GeneralPaperRoundedPowerQuery.scan unit p entries exponent acc := by
  induction entries generalizing exponent acc with
  | nil => rfl
  | cons entry rest ih =>
    rw [scan,GeneralPaperRoundedPowerQuery.scan]
    dsimp only
    split
    · rw [ih]
    · rw [ih]

theorem scan_work (unit p : ℕ) (entries : List Entry) (exponent : ℕ) (acc : Number) :
    (scan unit p entries exponent acc).2≤entries.length*(12*(p+1)+194)+16 := by
  induction entries generalizing exponent acc with
  | nil => simp only [scan,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons entry rest ih =>
    rw [scan]
    dsimp only
    split
    · have hp := GeneralPaperDyadicMultiply.multiply_work unit p acc entry.number
      have ht := ih (exponent-entry.degree) (GeneralPaperDyadicMultiply.multiply unit p acc entry.number).number
      dsimp only
      simp only [List.length_cons]
      nlinarith only [hp,ht]
    · have ht := ih exponent acc
      dsimp only
      simp only [List.length_cons]
      nlinarith only [ht]

def run (unit p : ℕ) (entries : List Entry) (exponent : ℕ) : GeneralPaperRoundedPowerQuery.Result × ℕ :=
  let answer := scan unit p entries exponent (one unit p)
  (⟨answer.1.number,answer.1.remaining,answer.1.work+8⟩,answer.2+64)

theorem data (unit p : ℕ) (entries : List Entry) (exponent : ℕ) :
    (run unit p entries exponent).1=GeneralPaperRoundedPowerQuery.evaluate unit p entries exponent := by
  simp only [run,scan_data,GeneralPaperRoundedPowerQuery.evaluate]

theorem work (unit p : ℕ) (entries : List Entry) (exponent : ℕ) :
    (run unit p entries exponent).2≤entries.length*(12*(p+1)+194)+80 := by
  have h := scan_work unit p entries exponent (one unit p)
  change (scan unit p entries exponent (one unit p)).2+64≤_
  omega

end Blotto.GeneralPaperPowerQueryArithmetic
