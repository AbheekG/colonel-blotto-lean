import Blotto.GeneralPaperDyadicFloat

/-! Actual normalized mantissa multiplication. Inputs carry encoded signed
exponents. Only their bounded integer mantissas are multiplied or divided;
no rational 2^exponent is evaluated. The quotient is computed by the retained
arithmetic-only bounded routine at the constructed precision depth.
-/
namespace Blotto.GeneralPaperDyadicMultiply
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Result where
  number : Number
  work : ℕ

def divisor (unit product : ℕ) : ℕ := if 2*unit*unit≤product then 2*unit else unit

def shift (unit product p : ℕ) : ℕ := if 2*unit*unit≤product then p+1 else p

def multiply (unit p : ℕ) (left right : Number) : Result :=
  if left.mantissa=0 ∨ right.mantissa=0 then ⟨zero,8⟩ else
    let product := left.mantissa*right.mantissa
    let quotient := GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)
    ⟨⟨quotient.quotient,left.exponent+right.exponent+(shift unit product p:ℤ)⟩,quotient.work+64⟩

theorem classification (unit product p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (hLow : unit*unit≤product) (hHigh : product<4*unit*unit) :
    0<divisor unit product ∧ unit*divisor unit product≤product ∧
      product<2*unit*divisor unit product ∧ divisor unit product=2^shift unit product p := by
  unfold divisor shift
  split
  · rename_i hLarge
    exact ⟨by omega,by nlinarith,by nlinarith,by rw [pow_succ,← hPower]; omega⟩
  · rename_i hSmall
    exact ⟨hUnit,hLow,by omega,hPower⟩

theorem mantissa_product_bounds (unit : ℕ) (left right : Number)
    (hl : unit≤left.mantissa ∧ left.mantissa<2*unit)
    (hr : unit≤right.mantissa ∧ right.mantissa<2*unit) :
    unit*unit≤left.mantissa*right.mantissa ∧ left.mantissa*right.mantissa<4*unit*unit := by
  constructor
  · exact Nat.mul_le_mul hl.1 hr.1
  · have h1 := Nat.mul_lt_mul_of_pos_right hl.2 (show 0<right.mantissa by omega)
    have h2 := Nat.mul_lt_mul_of_pos_left hr.2 (show 0<2*unit by omega)
    nlinarith

theorem quotient_spec (unit product p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (hLow : unit*unit≤product) (hHigh : product<4*unit*unit) :
    (product:ℚ)=(divisor unit product:ℚ)*
      (GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).quotient+
      (GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).remainder ∧
    0≤(GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).remainder ∧
      (GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).remainder<divisor unit product := by
  have hc := classification unit product p hUnit hPower hLow hHigh
  have hd : (0:ℚ)<divisor unit product := by exact_mod_cast hc.1
  apply GeneralPaperBoundedQuotient.run_spec _ _ hd (p+1) (by positivity)
  have he : (product:ℚ)<((2*unit*divisor unit product:ℕ):ℚ) := by exact_mod_cast hc.2.2.1
  have hPowerQ : (unit:ℚ)=(2:ℚ)^p := by exact_mod_cast hPower
  push_cast at he
  rw [hPowerQ] at he
  rw [pow_succ]
  nlinarith only [he]

theorem quotient_normal (unit product p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (hLow : unit*unit≤product) (hHigh : product<4*unit*unit) :
    unit≤(GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).quotient ∧
      (GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).quotient<2*unit := by
  have hc := classification unit product p hUnit hPower hLow hHigh
  have hs := quotient_spec unit product p hUnit hPower hLow hHigh
  have hd : (0:ℚ)<divisor unit product := by exact_mod_cast hc.1
  have hlo : (unit:ℚ)*(divisor unit product:ℚ)≤product := by exact_mod_cast hc.2.1
  have hhi : (product:ℚ)<2*(unit:ℚ)*(divisor unit product:ℚ) := by exact_mod_cast hc.2.2.1
  constructor
  · by_contra hn
    have hq : ((GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).quotient:ℚ)+1≤unit :=
      by exact_mod_cast (show (GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).quotient+1≤unit by omega)
    nlinarith only [hs.1,hs.2.2,hd,hlo,hq]
  · by_contra hn
    have hq : 2*(unit:ℚ)≤(GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).quotient :=
      by exact_mod_cast (show 2*unit≤(GeneralPaperBoundedQuotient.run (product:ℚ) (divisor unit product) (p+1)).quotient by omega)
    nlinarith only [hs.1,hs.2.1,hd,hhi,hq]

theorem multiply_normal (unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (left right : Number) (hl : Normal unit left) (hr : Normal unit right) :
    Normal unit (multiply unit p left right).number := by
  unfold multiply
  split
  · exact zero_normal unit
  · rename_i hNonzero
    have hl' := hl.resolve_left (by intro h; exact hNonzero (Or.inl h.1))
    have hr' := hr.resolve_left (by intro h; exact hNonzero (Or.inr h.1))
    have hp := mantissa_product_bounds unit left right hl' hr'
    exact Or.inr (quotient_normal unit _ p hUnit hPower hp.1 hp.2)

theorem multiply_work (unit p : ℕ) (left right : Number) : (multiply unit p left right).work≤12*(p+1)+66 := by
  unfold multiply
  split
  · dsimp only; omega
  · dsimp only
    rw [GeneralPaperBoundedQuotient.run_work]

theorem multiply_certificate (unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (left right : Number) (hl : Normal unit left) (hr : Normal unit right) :
    retention unit*(value left*value right)≤value (multiply unit p left right).number ∧
      value (multiply unit p left right).number≤value left*value right := by
  unfold multiply
  split
  · rename_i hZero
    rcases hZero with hz|hz <;> simp [value,zero,hz]
  · rename_i hNonzero
    have hl' := hl.resolve_left (by intro h; exact hNonzero (Or.inl h.1))
    have hr' := hr.resolve_left (by intro h; exact hNonzero (Or.inr h.1))
    let product := left.mantissa*right.mantissa
    let d := divisor unit product
    let r := GeneralPaperBoundedQuotient.run (product:ℚ) d (p+1)
    have hp := mantissa_product_bounds unit left right hl' hr'
    have hc := classification unit product p hUnit hPower hp.1 hp.2
    have hs := quotient_spec unit product p hUnit hPower hp.1 hp.2
    have hu : (0:ℚ)<unit := by exact_mod_cast hUnit
    have hlo : (unit:ℚ)*(d:ℚ)≤product := by exact_mod_cast hc.2.1
    have hr0 : 0≤r.remainder := hs.2.1
    have hre : r.remainder<(d:ℚ) := hs.2.2
    have hEq : (product:ℚ)=(d:ℚ)*(r.quotient:ℚ)+r.remainder := hs.1
    have hRelative : retention unit*(product:ℚ)≤(d:ℚ)*(r.quotient:ℚ) := by
      unfold retention
      apply (mul_le_mul_iff_right₀ hu).mp
      have hi : (1/(unit:ℚ))*(unit:ℚ)=1 := one_div_mul_cancel (ne_of_gt hu)
      nlinarith only [hlo,hre,hEq,hi]
    have hUpper : (d:ℚ)*(r.quotient:ℚ)≤product := by linarith only [hEq,hr0]
    have hScale : (0:ℚ)<(2:ℚ)^(left.exponent+right.exponent) := by positivity
    have hOut : value
        ⟨r.quotient,left.exponent+right.exponent+(shift unit product p:ℤ)⟩=
        ((d:ℚ)*(r.quotient:ℚ))*(2:ℚ)^(left.exponent+right.exponent) := by
      unfold value
      have hdPower : (d:ℚ)=(2:ℚ)^shift unit product p := by exact_mod_cast hc.2.2.2
      rw [zpow_add₀ (by norm_num),zpow_natCast,← hdPower]
      push_cast
      ring
    have hInput : value left*value right=(product:ℚ)*(2:ℚ)^(left.exponent+right.exponent) := by
      unfold value product
      rw [zpow_add₀ (by norm_num)]
      push_cast
      ring
    change retention unit*(value left*value right)≤value
        ⟨r.quotient,left.exponent+right.exponent+(shift unit product p:ℤ)⟩ ∧
      value ⟨r.quotient,left.exponent+right.exponent+(shift unit product p:ℤ)⟩≤value left*value right
    rw [hOut,hInput]
    constructor
    · have hm := mul_le_mul_of_nonneg_right hRelative hScale.le
      nlinarith only [hm]
    · exact mul_le_mul_of_nonneg_right hUpper hScale.le

theorem multiply_positive (unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (left right : Number) (hl : Normal unit left) (hr : Normal unit right)
    (hLeft : 0<left.mantissa) (hRight : 0<right.mantissa) :
    0<(multiply unit p left right).number.mantissa := by
  unfold multiply
  split
  · rename_i hz
    rcases hz with hz|hz <;> omega
  · dsimp only
    have hp := mantissa_product_bounds unit left right
      (hl.resolve_left (by intro h; omega)) (hr.resolve_left (by intro h; omega))
    have hq := quotient_normal unit _ p hUnit hPower hp.1 hp.2
    omega

end Blotto.GeneralPaperDyadicMultiply
