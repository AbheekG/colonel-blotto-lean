import Blotto.GeneralPaperCachedBitPairReferenceContract
import Blotto.GeneralPaperPositiveCeiling

/-! Bit-specific location of the original budget. One reduced integer
division replaces repeated full-input remainder tests. The complete old
quotient/remainder/work record is preserved; the real implementation stays
the bounded arithmetic quotient. Integer floor is a paper bit primitive. -/
namespace Blotto.GeneralPaperFastInputQuotient
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def floor (model : RationalCostModel) (W depth : ℕ) (x : ℚ) : GeneralPaperBoundedQuotient.Result×ℕ :=
  let n := x.num.natAbs
  let d := x.den
  let q := n/d
  (⟨q,x-(q:ℚ),12*depth+2⟩,
    model.rat (rationalWordWidth x)+GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n d+
    model.rat (rationalWordWidth (q:ℚ))+GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a-b) x (q:ℚ)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 12 depth+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (12*depth) 2+64*W)

theorem floor_value (model : RationalCostModel) (W depth : ℕ) (x : ℚ) (hx : 0≤x) :
    (floor model W depth x).1.quotient=⌊x⌋₊ := by
  change x.num.natAbs/x.den=⌊x⌋₊
  conv_rhs => rw [GeneralPaperPositiveCeiling.nonnegative_fraction x hx]
  exact (Rat.natFloor_natCast_div_natCast _ _).symm

theorem floor_data (model : RationalCostModel) (W depth : ℕ) (x : ℚ) (hx : 0≤x) (hCap : x<(2:ℚ)^depth) :
    (floor model W depth x).1=GeneralPaperBoundedQuotient.run x 1 depth := by
  have hq := (floor_value model W depth x hx).trans (GeneralPaperBoundedQuotient.run_floor x depth hx hCap).symm
  have hs := GeneralPaperBoundedQuotient.run_spec x 1 (by norm_num) depth hx (by simpa only [one_mul] using hCap)
  have hr : (GeneralPaperBoundedQuotient.run x 1 depth).remainder=x-((floor model W depth x).1.quotient:ℚ) := by
    rw [←hq] at hs
    linarith only [hs.1]
  have hw := GeneralPaperBoundedQuotient.run_work x 1 depth
  cases he : GeneralPaperBoundedQuotient.run x 1 depth with
  | mk q remainder work =>
    rw [he] at hq hr hw
    dsimp only at hq hr hw
    subst q;subst remainder;subst work
    rfl

def floorWidth (x : ℚ) (depth : ℕ) : ℕ := 64+8*rationalWordWidth x+16*depth

theorem floor_words (x : ℚ) (depth : ℕ) :
    1+binaryWordWidth x.num.natAbs≤floorWidth x depth ∧ 1+binaryWordWidth x.den≤floorWidth x depth ∧
      1+binaryWordWidth (x.num.natAbs/x.den)≤floorWidth x depth ∧
      rationalWordWidth (x.num.natAbs/x.den:ℕ)≤floorWidth x depth ∧
      rationalWordWidth (x-(x.num.natAbs/x.den:ℕ))≤floorWidth x depth := by
  have hq := binaryWordWidth_mono (Nat.div_le_self x.num.natAbs x.den)
  have hHeight := GeneralPaperBasisDivideBits.nat_height (x.num.natAbs/x.den)
  have hQ := rationalWordWidth_of_height hHeight
  have hR := rationalWordWidth_of_height ((rationalHeight_of_wordWidth x).sub hHeight)
  unfold floorWidth rationalWordWidth at *
  omega

theorem floor_work (model : RationalCostModel) (W depth : ℕ) (x : ℚ) :
    (floor model W depth x).2≤10*model.rat (floorWidth x depth)+64*W := by
  have hw := floor_words x depth
  have hx := model.monotone (show rationalWordWidth x≤floorWidth x depth by unfold floorWidth;omega)
  have hq := model.monotone hw.2.2.2.1
  have hdiv := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a/b)
    x.num.natAbs x.den (floorWidth x depth) hw.1 hw.2.1 hw.2.2.1
  have hsub := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b)
    x (x.num.natAbs/x.den:ℕ) (floorWidth x depth) (by unfold floorWidth;omega) hw.2.2.2.1 hw.2.2.2.2
  have hd := GeneralPaperInitializerControlCounters.word_le_self depth
  have h12 := GeneralPaperInitializerControlCounters.word_le_self (12*depth)
  have hLast := GeneralPaperInitializerControlCounters.word_le_self (12*depth+2)
  have hmul := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 12 depth (floorWidth x depth)
    (by change 5≤_;unfold floorWidth;omega) (by unfold floorWidth;omega) (by unfold floorWidth;omega)
  have hadd := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) (12*depth) 2 (floorWidth x depth)
    (by unfold floorWidth;omega) (by change 3≤_;unfold floorWidth;omega) (by unfold floorWidth;omega)
  unfold floor
  dsimp only
  omega

def run (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    GeneralPaperBoundedQuotient.Result×ℕ :=
  let scale : ℚ := c.proxy.Qg
  let x := b*scale
  let found := floor model W (c.proxy.gridBits+1) x
  (found.1,found.2+model.rat (rationalWordWidth scale)+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b scale+64*W)

theorem data (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1) :
    (run model W c b).1=(GeneralPaperProxyQuotientPrice.run model W c b).1 := by
  have hQ : (0:ℚ)<c.proxy.Qg := by rw [hc];exact_mod_cast GeneralPaperProxyParameters.grid_positive m k
  have hPow : (c.proxy.Qg:ℚ)=(2:ℚ)^c.proxy.gridBits := by
    rw [hc];exact_mod_cast GeneralPaperProxyParameters.grid_power m k
  rw [GeneralPaperProxyQuotientPrice.data]
  apply floor_data model W (c.proxy.gridBits+1) (b*c.proxy.Qg) (mul_nonneg hb.1.le hQ.le)
  rw [pow_succ,←hPow]
  nlinarith only [hb.2,hQ]

def width (m k B : ℕ) : ℕ :=
  256+32*B+32*binaryWordWidth (GeneralPaperProxyParameters.prepare m k).Qg+
    32*(GeneralPaperProxyParameters.prepare m k).gridBits

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ := 13*model.rat (width m k B)+128*W

theorem work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (B : ℕ) (hB : RationalHeight b B) :
    (run model W c b).2≤profile model W m k B := by
  let x := b*(c.proxy.Qg:ℚ)
  have hQHeight := GeneralPaperBasisDivideBits.nat_height c.proxy.Qg
  have hx := rationalWordWidth_of_height (hB.mul hQHeight)
  have hBWord := rationalWordWidth_of_height hB
  have hQWord := rationalWordWidth_of_height hQHeight
  have hFloor := floor_work model W (c.proxy.gridBits+1) x
  have hWidth : floorWidth x (c.proxy.gridBits+1)≤width m k B := by
    dsimp only [x] at *
    unfold floorWidth width
    rw [hc] at hx ⊢
    dsimp only [GeneralPaperPrecallCachePrice.specification] at hx ⊢
    omega
  have hF := Nat.mul_le_mul_left 10 (model.monotone hWidth)
  have hXCap : rationalWordWidth x≤width m k B := by
    unfold width;dsimp only [x] at *;rw [hc] at hx ⊢
    dsimp only [GeneralPaperPrecallCachePrice.specification] at hx ⊢
    omega
  have hBCap : rationalWordWidth b≤width m k B := by unfold width;omega
  have hQCap : rationalWordWidth (c.proxy.Qg:ℚ)≤width m k B := by
    unfold width;rw [hc] at hQWord ⊢
    dsimp only [GeneralPaperPrecallCachePrice.specification] at hQWord ⊢
    omega
  have hCast := model.monotone hQCap
  have hMul := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) b c.proxy.Qg
    (width m k B) hBCap hQCap hXCap
  unfold run profile
  change (floor model W (c.proxy.gridBits+1) x).2+model.rat (rationalWordWidth (c.proxy.Qg:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b c.proxy.Qg+64*W≤_
  omega

end Blotto.GeneralPaperFastInputQuotient
