import Blotto.GeneralPaperPositiveValueRounding

/-! Independent positive rational ceilings. The real path reads no input
encoding: adaptive doubling and remainder tests suffice. The bit path uses
one reduced numerator/denominator pair and explicitly priced div/mod/add.
The constructed cap is not a binary-length oracle. -/
namespace Blotto.GeneralPaperPositiveCeiling
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

theorem from_remainder (x r : ℚ) (q : ℕ) (he : x=(q:ℚ)+r) (hr : 0≤r) (hOne : r<1) :
    q+(if r=0 then 0 else 1)=⌈x⌉₊ := by
  by_cases hz : r=0
  · have hx : x=(q:ℚ) := by rw [he,hz,add_zero]
    simp only [hz,ite_true,Nat.add_zero,hx,Nat.ceil_natCast]
  · rw [ite_eq_right hz]
    apply Eq.symm
    apply (Nat.ceil_eq_iff (by omega : q+1≠0)).mpr
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    constructor <;> linarith only [he,hr,hOne,lt_of_le_of_ne hr (Ne.symm hz)]

def arithmetic (x : ℚ) (M : ℕ) : ℕ × ℕ :=
  let q := GeneralPaperGrowingQuotient.run x 1 (M+1)
  (q.quotient+(if q.remainder=0 then 0 else 1),q.work+32)

theorem cap (x : ℚ) (M : ℕ) (hx : x≤M) : x<(1:ℚ)*2^(M+1) := by
  have h : M<2^(M+1) := (Nat.lt_two_pow_self (n:=M)).trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega))
  have hc : (M:ℚ)<(2:ℚ)^(M+1) := by exact_mod_cast h
  simpa only [one_mul] using hx.trans_lt hc

theorem arithmetic_data (x : ℚ) (M : ℕ) (hx : 0≤x) (hM : x≤M) : (arithmetic x M).1=⌈x⌉₊ := by
  have hs := GeneralPaperGrowingQuotient.run_spec x 1 (by norm_num) (M+1) hx (cap x M hM)
  exact from_remainder x _ _ (by simpa only [one_mul] using hs.1) hs.2.1 hs.2.2

theorem arithmetic_work (x : ℚ) (M : ℕ) (hx : 0≤x) (hM : x≤M) :
    (arithmetic x M).2≤14*binaryWordWidth M+36 := by
  have hs := GeneralPaperGrowingQuotient.run_spec x 1 (by norm_num) (M+1) hx (cap x M hM)
  have hq : (GeneralPaperGrowingQuotient.run x 1 (M+1)).quotient≤M := by
    have h : ((GeneralPaperGrowingQuotient.run x 1 (M+1)).quotient:ℚ)≤M := by nlinarith only [hs.1,hs.2.1,hM]
    exact_mod_cast h
  have hw := GeneralPaperGrowingQuotient.work_word_bound x 1 (by norm_num) (M+1) hx (cap x M hM)
  have he := binaryWordWidth_mono hq
  unfold arithmetic
  dsimp only
  omega

def bits (model : RationalCostModel) (W : ℕ) (x : ℚ) : ℕ × ℕ :=
  let n := x.num.natAbs
  let d := x.den
  let q := n/d
  let r := n%d
  let bumped := q+1
  (if r=0 then q else bumped,
    model.rat (rationalWordWidth x)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n d+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) n d+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) q 1+
    model.rat (GeneralPaperNaturalPrimitivePrice.word r)+64*W)

theorem nonnegative_fraction (x : ℚ) (hx : 0≤x) : x=(x.num.natAbs:ℚ)/x.den := by
  have hn : (x.num.natAbs:ℤ)=x.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hx)
  have hq : (x.num.natAbs:ℚ)=(x.num:ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hn
  rw [hq,x.num_div_den]

theorem bits_data (model : RationalCostModel) (W : ℕ) (x : ℚ) (hx : 0≤x) : (bits model W x).1=⌈x⌉₊ := by
  let n := x.num.natAbs
  let d := x.den
  have hd : (0:ℚ)<d := by exact_mod_cast x.den_pos
  have hn : (n:ℚ)=(d:ℚ)*((n/d:ℕ):ℚ)+(n%d:ℕ) := by exact_mod_cast (Nat.div_add_mod n d).symm
  have he : x=((n/d:ℕ):ℚ)+(n%d:ℕ)/(d:ℚ) := by
    calc
      x=(n:ℚ)/(d:ℚ) := nonnegative_fraction x hx
      _=((d:ℚ)*((n/d:ℕ):ℚ)+(n%d:ℕ))/(d:ℚ) := by rw [←hn]
      _=((n/d:ℕ):ℚ)+(n%d:ℕ)/(d:ℚ) := by field_simp
  have hr : (0:ℚ)≤(n%d:ℕ)/(d:ℚ) := by positivity
  have hR : ((n%d:ℕ):ℚ)/(d:ℚ)<1 := (div_lt_one hd).mpr (by exact_mod_cast Nat.mod_lt n x.den_pos)
  have hc := from_remainder x (((n%d:ℕ):ℚ)/(d:ℚ)) (n/d) he hr hR
  have hz : (((n%d:ℕ):ℚ)/(d:ℚ)=0) ↔ n%d=0 := by simp only [div_eq_zero_iff,Nat.cast_eq_zero,hd.ne',or_false]
  unfold bits
  dsimp only
  change (if n%d=0 then n/d else n/d+1)=⌈x⌉₊
  by_cases h : n%d=0
  · simpa only [h,Nat.cast_zero,zero_div,ite_true,Nat.add_zero] using hc
  · have hf : ((n%d:ℕ):ℚ)/(d:ℚ)≠0 := fun hf => h (hz.mp hf)
    simpa only [h,hf,ite_false] using hc

def width (x : ℚ) : ℕ := 4+rationalWordWidth x

theorem bits_work (model : RationalCostModel) (W : ℕ) (x : ℚ) :
    (bits model W x).2≤8*model.rat (width x)+64*W := by
  let n := x.num.natAbs
  let d := x.den
  let C := n+d+1
  have hw : 1+binaryWordWidth C≤width x := by
    have ha := GeneralPaperReferenceScaling.word_add n d
    have hb := GeneralPaperReferenceScaling.word_add (n+d) 1
    rw [show binaryWordWidth 1=1 by decide] at hb
    unfold C width rationalWordWidth
    dsimp only [n,d] at ha hb ⊢
    omega
  have hq := Nat.div_le_self n d
  have hr := Nat.mod_le n d
  have hnC : n≤C := by unfold C; omega
  have hdC : d≤C := by unfold C; omega
  have hqC : n/d≤C := hq.trans hnC
  have hrC : n%d≤C := hr.trans hnC
  have hOne : 1≤C := by unfold C; omega
  have hBump : n/d+1≤C := by unfold C; omega
  have hDiv := (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) n d C hnC hdC hqC).trans
    (Nat.mul_le_mul_left 2 (model.monotone hw))
  have hMod := (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a%b) n d C hnC hdC hrC).trans
    (Nat.mul_le_mul_left 2 (model.monotone hw))
  have hAdd := (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) (n/d) 1 C hqC hOne hBump).trans
    (Nat.mul_le_mul_left 2 (model.monotone hw))
  have hRead := model.monotone (show rationalWordWidth x≤width x by unfold width; omega)
  have hTest := model.monotone ((Nat.add_le_add_left (binaryWordWidth_mono hrC) 1).trans hw)
  unfold bits
  dsimp only
  change model.rat (rationalWordWidth x)+GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n d+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) n d+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (n/d) 1+
    model.rat (GeneralPaperNaturalPrimitivePrice.word (n%d))+64*W≤_
  unfold GeneralPaperNaturalPrimitivePrice.word
  omega

end Blotto.GeneralPaperPositiveCeiling
