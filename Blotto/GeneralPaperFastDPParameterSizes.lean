import Blotto.GeneralPaperFastParameterPowerPrice

/-! The native DP grid size, depth and option count have the paper's single
inverse-accuracy power, up to polynomial logarithmic factors in M. These
follow from the actual constructed profit/source parameters, including m=0.
They are analytical bounds and add no constructor or validation pass. -/
namespace Blotto.GeneralPaperFastDPParameterSizes
open GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem measure_positive (m lambda k Qv : ℕ) : 128≤measure m lambda k Qv := by
  unfold GeneralPaperSourcePreparationSizes.measure
  omega

theorem height_plus (m lambda k Qv : ℕ) :
    (GeneralPaperProfitParameters.parameters m lambda k Qv).height+1≤measure m lambda k Qv := by
  have hh := GeneralPaperFastOrderedDPPrice.height_bound m lambda k Qv
  have hw := binaryWordWidth_mono (show m≤m+1 by omega)
  unfold GeneralPaperSourcePreparationSizes.measure
  omega

theorem width_bound (m lambda k Qv : ℕ) :
    (GeneralPaperProfitParameters.parameters m lambda k Qv).width≤8*measure m lambda k Qv*2^(25+k) := by
  have hn := GeneralPaperProfitParameters.width_target_upper m lambda k Qv
  have hh := Nat.mul_le_mul_right (2^(25+k)) (Nat.mul_le_mul_left 8 (height_plus m lambda k Qv))
  nlinarith only [hn,hh]

def gridCap (m lambda k Qv : ℕ) : ℕ := 2^34*(measure m lambda k Qv)^2*2^k

theorem grid_size (m lambda k Qv : ℕ) :
    (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size≤gridCap m lambda k Qv := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let M := measure m lambda k Qv
  let A := 2^(25+k)
  have hM : 128≤M := measure_positive m lambda k Qv
  have hA : 1≤A := Nat.one_le_pow _ _ (by decide)
  have hw := width_bound m lambda k Qv
  change p.width≤8*M*A at hw
  have he := (GeneralPaperProfitGridEnvelope.sizes m lambda k Qv).exponent
  change p.exponent≤32*M at he
  have hp := Nat.mul_le_mul (show p.exponent+1≤33*M by omega) hw
  have hn := GeneralPaperProfitGridPrepare.size_bound p.qProf p.width p.exponent
  change (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size≤(p.exponent+1)*p.width+2 at hn
  have hpos : 1≤M^2*A := by
    have h := Nat.mul_pos (pow_pos (by omega : 0<M) 2) (by omega : 0<A)
    omega
  have hbound : (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size≤512*M^2*A := by
    nlinarith only [hp,hn,hpos]
  exact hbound.trans_eq (by dsimp only [gridCap,A]; rw [pow_add]; norm_num; ring)

theorem grid_word (m lambda k Qv : ℕ) :
    binaryWordWidth ((GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size+1)≤64*measure m lambda k Qv := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  have hn := GeneralPaperProfitGridPrepare.size_bound p.qProf p.width p.exponent
  have hc := (GeneralPaperProfitGridEnvelope.sizes m lambda k Qv).capacity
  have hcap : (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size+1≤GeneralPaperProfitOrderPrice.capacity p.width p.exponent := by
    change (GeneralPaperProfitGridPrepare.prepare p.qProf p.width p.exponent).size+1≤_
    unfold GeneralPaperProfitOrderPrice.capacity
    nlinarith only [hn,Nat.zero_le p.exponent]
  exact (binaryWordWidth_mono hcap).trans hc

theorem grid_depth (m lambda k Qv : ℕ) :
    (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.depth≤64*measure m lambda k Qv := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  have hh : (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.depth≤
      binaryWordWidth ((GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size+1) :=
    GeneralPaperPowerCeiling.ceiling_minimal _ _ (lt_pow_binaryWordWidth _).le
  exact hh.trans (grid_word m lambda k Qv)

def optionCap (k : ℕ) : ℕ := 2^36*2^k

theorem options (k : ℕ) : (GeneralPaperSourceParameters.prepare k).summarySize+2≤optionCap k := by
  rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
  have hp : 1≤2^k := Nat.one_le_pow _ _ (by decide)
  unfold optionCap
  rw [pow_add]
  norm_num
  omega

end Blotto.GeneralPaperFastDPParameterSizes
