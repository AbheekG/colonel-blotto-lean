import Blotto.GeneralPaperDyadicAddition

/-! Exact shifts of encoded dyadic exponents, including uniform interval
mass and virtual halving during quantile descent. Runtime constructs no
integer or rational 2^height for an exponentially large code interval.
-/
namespace Blotto.GeneralPaperDyadicShift
open GeneralPaperDyadicFloat
set_option autoImplicit false

def shift (x : Number) (amount : ℤ) : Number :=
  if x.mantissa=0 then zero else ⟨x.mantissa,x.exponent+amount⟩

def uniformMass (unit p height : ℕ) : Number := ⟨unit,(height:ℤ)-(p:ℤ)⟩

theorem shift_value (x : Number) (amount : ℤ) : value (shift x amount)=value x*(2:ℚ)^amount := by
  unfold shift
  split
  · rename_i hz
    simp [value,zero,hz]
  · simp only [value,zpow_add₀ (by norm_num : (2:ℚ)≠0)]
    ring

theorem shift_normal (unit : ℕ) (x : Number) (amount : ℤ) (hNormal : Normal unit x) :
    Normal unit (shift x amount) := by
  unfold shift
  split
  · exact zero_normal unit
  · rename_i hz
    exact Or.inr (hNormal.resolve_left (by intro h; exact hz h.1))

theorem shift_positive (x : Number) (amount : ℤ) (hPositive : 0<x.mantissa) :
    (shift x amount).mantissa=x.mantissa := by
  simp only [shift,show ¬x.mantissa=0 by omega,ite_false]

theorem uniform_normal (unit p height : ℕ) (hUnit : 0<unit) : Normal unit (uniformMass unit p height) :=
  Or.inr ⟨le_refl _,by dsimp [uniformMass]; omega⟩

theorem uniform_positive (unit p height : ℕ) (hUnit : 0<unit) :
    0<(uniformMass unit p height).mantissa := hUnit

theorem uniform_value (unit p height : ℕ) (hPower : unit=2^p) :
    value (uniformMass unit p height)=(2:ℚ)^height := by
  unfold value uniformMass
  rw [zpow_sub₀ (by norm_num),zpow_natCast,zpow_natCast]
  have hu : (unit:ℚ)=(2:ℚ)^p := by exact_mod_cast hPower
  rw [hu]
  field_simp

theorem half_value (x : Number) : value (shift x (-1))=value x/2 := by
  rw [shift_value]
  norm_num
  ring

theorem uniform_half (unit p height : ℕ) (hPower : unit=2^p) :
    value (shift (uniformMass unit p (height+1)) (-1))=value (uniformMass unit p height) := by
  rw [half_value,uniform_value unit p (height+1) hPower,uniform_value unit p height hPower,pow_succ]
  ring

end Blotto.GeneralPaperDyadicShift
