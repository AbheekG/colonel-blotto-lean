import Blotto.GeneralPaperProxyQuotientCast
import Blotto.GeneralPaperParameterCounterWords

/-! Rational implementation of the classifier's original-budget cell
location. Reuse the retained scale/depth, cast and multiply once, then call
the existing priced bounded quotient. The native real result is exact.
Input rational height stays explicit until original-input preparation.
-/
namespace Blotto.GeneralPaperProxyQuotientPrice
set_option autoImplicit false
set_option maxHeartbeats 4000000

def word (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) : ℕ := W+c.proxy.gridBits+32

def run (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    GeneralPaperBoundedQuotient.Result × ℕ :=
  let Q := c.proxy.Qg
  let location := GeneralPaperBoundedQuotient.runWithBits model (word W c) (b*(Q:ℚ)) 1 (c.proxy.gridBits+1)
  (location.1,location.2+model.rat (rationalWordWidth (Q:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b (Q:ℚ)+64*W)

theorem data (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    (run model W c b).1=GeneralPaperBoundedQuotient.run (b*(c.proxy.Qg:ℚ)) 1 (c.proxy.gridBits+1) :=
  GeneralPaperBoundedQuotient.run_data model (word W c) _ _ _

theorem real_data (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) :
    GeneralPaperProxyQuotientCast.lift (run model W c b).1=GeneralPaperProxyQuotient.locate m k (b:ℝ) := by
  rw [data]
  subst c
  exact GeneralPaperProxyQuotientCast.locate_data m k b

def width (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) : ℕ :=
  1+2*(B+binaryWordWidth c.proxy.Qg+2)

def profile (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) : ℕ :=
  GeneralPaperBoundedQuotient.bitProfile model (word W c) (B+binaryWordWidth c.proxy.Qg) 1 (c.proxy.gridBits+1)+
    3*model.rat (width c B)+64*W

def envelope (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) : ℕ :=
  64+4*B+4*binaryWordWidth c.proxy.Qg+8*c.proxy.gridBits

theorem profile_bound (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) :
    profile model W c B≤256*(c.proxy.gridBits+2)*(W+model.rat (envelope c B)) := by
  let L := envelope c B
  let P := model.rat L
  let F := W+P
  have hCounter : c.proxy.gridBits+32≤P :=
    (show c.proxy.gridBits+32≤L by dsimp [L,envelope]; omega).trans (model.word_le L)
  have hChild : model.rat (1+2*GeneralPaperBoundedQuotient.heightBudget
      (B+binaryWordWidth c.proxy.Qg) 1 (c.proxy.gridBits+1))≤P :=
    model.monotone (by dsimp [L,envelope,GeneralPaperBoundedQuotient.heightBudget]; omega)
  have hRaw : model.rat (width c B)≤P := model.monotone (by dsimp [width,L,envelope]; omega)
  have hLocal : word W c≤F := by dsimp [word,F]; omega
  have hMain : 64*word W c+6*model.rat (1+2*GeneralPaperBoundedQuotient.heightBudget
      (B+binaryWordWidth c.proxy.Qg) 1 (c.proxy.gridBits+1))≤128*F := by
    dsimp [F]
    omega
  have hMul := Nat.mul_le_mul_left (c.proxy.gridBits+2) hMain
  have hExtra : 3*model.rat (width c B)+64*W≤128*F := by dsimp [F]; omega
  have hFactor : 128*F≤128*(c.proxy.gridBits+2)*F := by
    nlinarith only [Nat.zero_le (c.proxy.gridBits*F)]
  change (c.proxy.gridBits+2)*(64*word W c+6*model.rat
    (1+2*GeneralPaperBoundedQuotient.heightBudget (B+binaryWordWidth c.proxy.Qg) 1 (c.proxy.gridBits+1)))+
    3*model.rat (width c B)+64*W≤256*(c.proxy.gridBits+2)*F
  nlinarith only [hMul,hExtra,hFactor]

theorem work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (run model W c b).2≤profile model W c B := by
  subst c
  let c := GeneralPaperPrecallCachePrice.specification m k
  let Q := c.proxy.Qg
  let w := c.proxy.gridBits+1
  let L := width c B
  have hQ : (0:ℚ)<Q := by exact_mod_cast GeneralPaperProxyParameters.grid_positive m k
  have hPow : (Q:ℚ)=(2:ℚ)^c.proxy.gridBits := by exact_mod_cast GeneralPaperProxyParameters.grid_power m k
  have hX : 0≤b*(Q:ℚ) := mul_nonneg hb.1.le hQ.le
  have hCap : b*(Q:ℚ)<1*(2:ℚ)^w := by
    dsimp only [w]
    rw [pow_succ,←hPow]
    nlinarith only [hb.2,hQ]
  have hQHeight : RationalHeight (Q:ℚ) (binaryWordWidth Q) := GeneralPaperBasisDivideBits.nat_height Q
  have hXHeight := hB.mul hQHeight
  have hOne : RationalHeight 1 1 := by norm_num [RationalHeight]
  have hl := GeneralPaperBoundedQuotient.run_bit_work model (word W c) (b*(Q:ℚ)) 1 (by norm_num) w
    (B+binaryWordWidth Q) 1 hX hCap hXHeight hOne
  have hInput : rationalWordWidth b≤L := (rationalWordWidth_of_height hB).trans (by dsimp [L,width,Q]; omega)
  have hScale : rationalWordWidth (Q:ℚ)≤L := (rationalWordWidth_of_height hQHeight).trans (by dsimp [L,width,Q]; omega)
  have hProduct : rationalWordWidth (b*(Q:ℚ))≤L := (rationalWordWidth_of_height hXHeight).trans (by dsimp [L,width,Q]; omega)
  have hCast := model.monotone hScale
  have hMul := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) b (Q:ℚ) L hInput hScale hProduct
  change (GeneralPaperBoundedQuotient.runWithBits model (word W c) (b*(Q:ℚ)) 1 w).2+
    model.rat (rationalWordWidth (Q:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b (Q:ℚ)+64*W≤_
  change _≤GeneralPaperBoundedQuotient.bitProfile model (word W c) (B+binaryWordWidth Q) 1 w+3*model.rat L+64*W
  dsimp only [c,Q,w,L] at *
  omega

theorem bounded_work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (run model W c b).2≤256*(c.proxy.gridBits+2)*(W+model.rat (envelope c B)) :=
  (work model W m k c hc b hb B hB).trans (profile_bound model W c B)

theorem raw_counter_words (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (x a : ℚ)
    (depth : ℕ) (hDepth : depth≤c.proxy.gridBits+1) :
    binaryWordWidth (2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient)≤word W c ∧
    binaryWordWidth (2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient+1)≤word W c ∧
    binaryWordWidth ((GeneralPaperBoundedQuotient.run x a depth).work+12)≤word W c := by
  obtain ⟨h0,h1⟩ := GeneralPaperInitializerRoundingBits.raw_quotient_words x a depth (word W c)
    (by dsimp [word]; omega)
  have hWork := GeneralPaperBoundedQuotient.run_work x a depth
  have hUpper : (GeneralPaperBoundedQuotient.run x a depth).work+12≤12*(c.proxy.gridBits+1)+194 := by omega
  have hb := binaryWordWidth_mono hUpper
  have hl := GeneralPaperParameterCounterWords.linear_word (c.proxy.gridBits+1)
  have hs := GeneralPaperInitializerControlCounters.word_le_self (c.proxy.gridBits+1)
  refine ⟨h0,h1,?_⟩
  unfold word
  omega

theorem quotient_cell (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1) :
    (run model W c b).1.quotient<c.proxy.Qg ∧
    (((run model W c b).1.quotient:ℝ)/(c.proxy.Qg:ℝ))≤(b:ℝ) ∧
    (b:ℝ)<(((run model W c b).1.quotient:ℝ)+1)/(c.proxy.Qg:ℝ) := by
  have hQuot := congrArg GeneralPaperProxyQuotient.Result.quotient (real_data model W m k c hc b)
  change (run model W c b).1.quotient=(GeneralPaperProxyQuotient.locate m k (b:ℝ)).quotient at hQuot
  have hReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  have hs := GeneralPaperProxyQuotient.locate_spec m k (b:ℝ) hReal
  rw [hQuot,hc]
  exact hs

end Blotto.GeneralPaperProxyQuotientPrice
