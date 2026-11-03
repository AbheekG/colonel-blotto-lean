import Blotto.GeneralPaperQuotientConstructionStorage

/-! Actual original-budget cell location: one shared input, scale/product,
native quotient return, retained descent frames and primitive scratch.
The explicit input-height term is outside the recursive frame multiplier. -/
namespace Blotto.GeneralPaperProxyLocationStorage
open GeneralPaperEncodedScalarStorage GeneralPaperQuotientConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def window (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) : ℕ :=
  rationalWordWidth b+rationalWordWidth (c.proxy.Qg:ℚ)+rationalWordWidth (b*(c.proxy.Qg:ℚ))+
    peak model (GeneralPaperProxyQuotientPrice.word W c) (b*(c.proxy.Qg:ℚ)) 1 (c.proxy.gridBits+1)+
      record W (GeneralPaperProxyQuotientPrice.run model W c b).1+
      model.rat (rationalWordWidth (c.proxy.Qg:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b (c.proxy.Qg:ℚ)+
      fields W [c.proxy.Qg,c.proxy.gridBits+1]+128*W

def profile (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) : ℕ :=
  let d := c.proxy.gridBits+1
  let A := B+binaryWordWidth c.proxy.Qg
  let V := GeneralPaperProxyQuotientPrice.word W c
  let E := GeneralPaperProxyQuotientPrice.envelope c B
  (d+1)*frameCap V 1 d+localCap model V A 1 d+16*E+512*W+4*model.rat E

theorem bounded (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) : window model W c b≤profile model W c B := by
  let Q := c.proxy.Qg
  let d := c.proxy.gridBits+1
  let A := B+binaryWordWidth Q
  let E := GeneralPaperProxyQuotientPrice.envelope c B
  have hQ : 0<Q := by dsimp only [Q]; rw [hc]; exact GeneralPaperProxyParameters.grid_positive m k
  have hQrat : (0:ℚ)<Q := by exact_mod_cast hQ
  have hpow : (Q:ℚ)=(2:ℚ)^c.proxy.gridBits := by
    dsimp only [Q]
    rw [hc]
    exact_mod_cast GeneralPaperProxyParameters.grid_power m k
  have hcap : b*(Q:ℚ)<1*(2:ℚ)^d := by
    dsimp only [d]
    rw [pow_succ,←hpow]
    nlinarith only [hb.2,hQrat]
  have hx : 0≤b*(Q:ℚ) := mul_nonneg hb.1.le hQrat.le
  have hscale := GeneralPaperBasisDivideBits.nat_height Q
  have hproduct : RationalHeight (b*(Q:ℚ)) A := hB.mul hscale
  have hone : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
  have hp := GeneralPaperQuotientConstructionStorage.bounded model (GeneralPaperProxyQuotientPrice.word W c)
    (b*(Q:ℚ)) 1 (by norm_num) d A 1 hx hcap hproduct hone
  have hr := record_bound W (b*(Q:ℚ)) 1 (by norm_num) d A 1 hx hcap hproduct hone
  have hH : 1+2*GeneralPaperBoundedQuotient.heightBudget A 1 d≤E := by
    dsimp [A,d,E,GeneralPaperProxyQuotientPrice.envelope,Q,GeneralPaperBoundedQuotient.heightBudget]
    omega
  have hi : rationalWordWidth b≤E := (rationalWordWidth_of_height hB).trans (by
    dsimp [E,GeneralPaperProxyQuotientPrice.envelope]; omega)
  have hq : rationalWordWidth (Q:ℚ)≤E := (rationalWordWidth_of_height hscale).trans (by
    dsimp [E,GeneralPaperProxyQuotientPrice.envelope,Q]; omega)
  have hm : rationalWordWidth (b*(Q:ℚ))≤E := (rationalWordWidth_of_height hproduct).trans (by
    dsimp [A,E,GeneralPaperProxyQuotientPrice.envelope,Q]; omega)
  have hcast := model.monotone hq
  have hmul := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b)
    b (Q:ℚ) E hi hq hm
  have hd := GeneralPaperInitializerControlCounters.word_le_self (c.proxy.gridBits+1)
  have hfields := fields_bound W E [Q,c.proxy.gridBits+1] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> unfold natBits <;>
      dsimp [E,GeneralPaperProxyQuotientPrice.envelope,Q] <;> omega)
  change _≤2*(E+W)+32*W at hfields
  unfold window profile
  rw [GeneralPaperProxyQuotientPrice.data]
  change rationalWordWidth b+rationalWordWidth (Q:ℚ)+rationalWordWidth (b*(Q:ℚ))+
    peak model (GeneralPaperProxyQuotientPrice.word W c) (b*(Q:ℚ)) 1 d+
      record W (GeneralPaperBoundedQuotient.run (b*(Q:ℚ)) 1 d)+model.rat (rationalWordWidth (Q:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b (Q:ℚ)+
        fields W [Q,c.proxy.gridBits+1]+128*W≤
    (d+1)*frameCap (GeneralPaperProxyQuotientPrice.word W c) 1 d+
      localCap model (GeneralPaperProxyQuotientPrice.word W c) A 1 d+16*E+512*W+4*model.rat E
  omega

end Blotto.GeneralPaperProxyLocationStorage
