import Blotto.GeneralPaperCFLinearInvariant

/-! The continuant determinant alternates sign and has absolute value one.
Consequently every positive current denominator is already reduced. The
assertions concern the actual arithmetic loop, including rejected candidates.
-/
namespace Blotto.GeneralPaperCFDeterminant
open GeneralPaperRegularCFLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Unimodular (s : State) : Prop :=
  s.previousNum*s.olderDen=s.olderNum*s.previousDen+1 ∨
    s.olderNum*s.previousDen=s.previousNum*s.olderDen+1

theorem initial_unimodular (C t : ℕ) : Unimodular (initial C t) := by
  left
  rfl

theorem update_unimodular (a p q oldP oldQ : ℕ)
    (h : p*oldQ=oldP*q+1 ∨ oldP*q=p*oldQ+1) :
    (a*p+oldP)*q=p*(a*q+oldQ)+1 ∨ p*(a*q+oldQ)=(a*p+oldP)*q+1 := by
  rcases h with h|h
  · right
    nlinarith only [h]
  · left
    nlinarith only [h]

theorem advance_unimodular (D divisionFuel : ℕ) (s : State) (h : Unimodular s) :
    Unimodular (advance D divisionFuel s).1 := by
  by_cases hz : s.denominator=0
  · simpa only [advance,ite_eq_left hz,Unimodular] using h
  · have he := update_unimodular (GeneralPaperConstructedNatDivision.run s.numerator s.denominator divisionFuel).quotient
      s.previousNum s.previousDen s.olderNum s.olderDen h
    simp only [advance,ite_eq_right hz]
    split
    · split <;> exact he
    · exact he

theorem run_unimodular (D divisionFuel fuel : ℕ) (s : State) (h : Unimodular s) :
    Unimodular (run D divisionFuel fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    have he := advance_unimodular D divisionFuel s h
    dsimp only [run]
    split
    · exact ih _ he
    · exact he

theorem previous_coprime (s : State) (h : Unimodular s) : Nat.Coprime s.previousNum s.previousDen := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  apply Nat.dvd_one.mp
  have ha : Nat.gcd s.previousNum s.previousDen∣s.previousNum*s.olderDen :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
  have hb : Nat.gcd s.previousNum s.previousDen∣s.olderNum*s.previousDen :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  rcases h with h|h
  · have he : Nat.gcd s.previousNum s.previousDen∣s.olderNum*s.previousDen+1 := h ▸ ha
    exact (Nat.dvd_add_iff_right hb).mpr he
  · have he : Nat.gcd s.previousNum s.previousDen∣s.previousNum*s.olderDen+1 := h ▸ hb
    exact (Nat.dvd_add_iff_right ha).mpr he

theorem previous_reduced_den (s : State) (h : Unimodular s) (hd : 0<s.previousDen) :
    ((s.previousNum:ℚ)/s.previousDen).den=s.previousDen := by
  have he := Rat.den_div_eq_of_coprime (a := (s.previousNum:ℤ)) (b := (s.previousDen:ℤ))
    (by exact_mod_cast hd) (by simpa only [Int.natAbs_natCast] using previous_coprime s h)
  have hh : ((((s.previousNum:ℚ)/s.previousDen).den:ℕ):ℤ)=(s.previousDen:ℤ) := by
    simpa only [Int.cast_natCast] using he
  exact_mod_cast hh

end Blotto.GeneralPaperCFDeterminant
