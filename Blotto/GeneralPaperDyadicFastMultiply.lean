import Blotto.GeneralPaperFastConstructedDivision

/-! The bit-model dyadic product shares the product, threshold and branch,
then divides constructed integer mantissas. The entire old result agrees,
including zero branches and native metadata. Encoded exponents are added
as integers; rational valuations appear only in the specification proofs.
-/
namespace Blotto.GeneralPaperDyadicFastMultiply
open GeneralPaperDyadicFloat GeneralPaperDyadicMultiply
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (unit p : ℕ) (left right : Number) : GeneralPaperDyadicMultiply.Result :=
  if left.mantissa=0 ∨ right.mantissa=0 then ⟨zero,8⟩ else
    let product := left.mantissa*right.mantissa
    let large := decide (2*unit*unit≤product)
    let divisor := if large then 2*unit else unit
    let shift := if large then p+1 else p
    ⟨⟨product/divisor,left.exponent+right.exponent+(shift:ℤ)⟩,12*(p+1)+66⟩

theorem data (unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p) (left right : Number)
    (hl : Normal unit left) (hr : Normal unit right) : run unit p left right=multiply unit p left right := by
  by_cases hz : left.mantissa=0 ∨ right.mantissa=0
  · simp only [run,multiply,ite_eq_left hz]
  · have hl' := hl.resolve_left (by intro h; exact hz (Or.inl h.1))
    have hr' := hr.resolve_left (by intro h; exact hz (Or.inr h.1))
    have hProd := mantissa_product_bounds unit left right hl' hr'
    have hc := classification unit (left.mantissa*right.mantissa) p hUnit hPower hProd.1 hProd.2
    have hCap : left.mantissa*right.mantissa<divisor unit (left.mantissa*right.mantissa)*2^(p+1) := by
      rw [pow_succ,←hPower]
      nlinarith only [hc.2.2.1]
    have hQ := GeneralPaperFastConstructedDivision.quotient_data
      (left.mantissa*right.mantissa) (divisor unit (left.mantissa*right.mantissa)) (p+1) hc.1 hCap
    rw [run,multiply,ite_eq_right hz,ite_eq_right hz]
    dsimp only
    rw [hQ,GeneralPaperBoundedQuotient.run_work]
    simp only [decide_eq_true_eq]
    unfold divisor shift
    split <;> dsimp only

theorem exponent_bound (unit p : ℕ) (left right : Number) :
    (multiply unit p left right).number.exponent.natAbs≤left.exponent.natAbs+right.exponent.natAbs+p+1 := by
  unfold multiply
  split
  · change (0:ℤ).natAbs≤_
    simp only [Int.natAbs_zero]
    omega
  · dsimp only
    have ha := Int.natAbs_add_le left.exponent right.exponent
    have hb := Int.natAbs_add_le (left.exponent+right.exponent) (shift unit (left.mantissa*right.mantissa) p:ℤ)
    have hs : shift unit (left.mantissa*right.mantissa) p≤p+1 := by unfold shift; split <;> omega
    simp only [Int.natAbs_natCast] at hb
    omega

end Blotto.GeneralPaperDyadicFastMultiply
