import Blotto.GeneralPaperCDFMesh

/-! Positive dyadic storage for the selected source. A mantissa m in
[2^p,2^(p+1)) has p+1 significant bits; the paper's unit roundoff is 2^(-p).
The rational valuation is a proof/reference semantics, never expanded by the
stored arithmetic. A zero marker has mantissa and exponent both zero.
-/
namespace Blotto.GeneralPaperDyadicFloat
set_option autoImplicit false

structure Number where
  mantissa : ℕ
  exponent : ℤ
deriving DecidableEq

def value (x : Number) : ℚ := (x.mantissa:ℚ)*(2:ℚ)^x.exponent

def Normal (unit : ℕ) (x : Number) : Prop :=
  (x.mantissa=0 ∧ x.exponent=0) ∨ (unit≤x.mantissa ∧ x.mantissa<2*unit)

def zero : Number := ⟨0,0⟩

def one (unit p : ℕ) : Number := ⟨unit,-(p:ℤ)⟩

def retention (unit : ℕ) : ℚ := 1-1/(unit:ℚ)

theorem zero_value : value zero=0 := by simp [value,zero]

theorem value_nonnegative (x : Number) : 0≤value x := by unfold value; positivity

theorem value_positive (x : Number) (h : 0<x.mantissa) : 0<value x := by unfold value; positivity

theorem value_zero_iff (x : Number) : value x=0 ↔ x.mantissa=0 := by
  unfold value
  have hp : (2:ℚ)^x.exponent≠0 := by positivity
  simp only [mul_eq_zero,hp,or_false,Nat.cast_eq_zero]

theorem zero_normal (unit : ℕ) : Normal unit zero := Or.inl ⟨rfl,rfl⟩

theorem one_normal (unit p : ℕ) (hUnit : 0<unit) : Normal unit (one unit p) := by
  exact Or.inr ⟨le_refl _,by dsimp [one]; omega⟩

theorem one_value (unit p : ℕ) (hUnit : unit=2^p) : value (one unit p)=1 := by
  unfold value one
  rw [hUnit,Nat.cast_pow,Nat.cast_ofNat,zpow_neg,zpow_natCast,mul_inv_cancel₀ (by positivity)]

theorem retention_bounds (unit : ℕ) (hUnit : 1<unit) : 0<retention unit ∧ retention unit≤1 := by
  have hu : (1:ℚ)<unit := by exact_mod_cast hUnit
  unfold retention
  have hi : 0<(1/(unit:ℚ)) := by positivity
  have hl : 1/(unit:ℚ)<1 := (div_lt_one (by linarith)).mpr (by linarith)
  constructor <;> linarith

theorem normal_mantissa_bits (p : ℕ) (x : Number) (h : Normal (2^p) x) : x.mantissa<2^(p+1) := by
  rcases h with h|h
  · rw [h.1]; positivity
  · rw [pow_succ]
    omega

end Blotto.GeneralPaperDyadicFloat
