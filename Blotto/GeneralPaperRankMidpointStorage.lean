import Blotto.GeneralPaperSourceRefinementResidentRates
import Blotto.GeneralPaperQuotientConstructionStorage

/-! The literal arithmetic rank midpoint, including its bounded-quotient
stack, rational sum and cast values, returned record and native metadata.
N/depth are erased analytical bounds on reached index values. No division,
floor, input-length or capacity oracle is supplied to the data path. -/
namespace Blotto.GeneralPaperRankMidpointStorage
open GeneralPaperEncodedScalarStorage GeneralPaperQuotientConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def argumentHeight (N : ℕ) : ℕ := 2*binaryWordWidth N+1
def metadataCap (W depth N : ℕ) : ℕ := 2*N+depth+1+(12*depth+2)+(12*depth+2)*W

def window (model : RationalCostModel) (W depth lo hi : ℕ) : ℕ :=
  let x := (lo:ℚ)+hi
  let result := GeneralPaperRankMidpoint.midpoint depth lo hi
  peak model W x 2 depth+record W result+
    rationalWordWidth (lo:ℚ)+rationalWordWidth (hi:ℚ)+rationalWordWidth x+
    GeneralPaperScoreBitPrimitive.additionPrice model (lo:ℚ) hi+
    fields W [depth,lo,hi,lo+hi,result.quotient,result.work,result.work*W]+256*W

def profile (model : RationalCostModel) (W depth N : ℕ) : ℕ :=
  let A := argumentHeight N
  let H := 1+2*GeneralPaperBoundedQuotient.heightBudget A 2 depth
  (depth+1)*frameCap W 2 depth+localCap model W A 2 depth+(4*H+128*W)+
    3*(1+2*A)+2*model.rat (1+2*A)+7*(natBits (metadataCap W depth N)+W)+32*W+256*W

theorem bounded (model : RationalCostModel) (W depth N lo hi : ℕ) (hOrder : lo≤hi) (hHi : hi≤N) (hSize : N<2^depth) :
    window model W depth lo hi≤profile model W depth N := by
  let x := (lo:ℚ)+hi
  let result := GeneralPaperRankMidpoint.midpoint depth lo hi
  have hLo := (GeneralPaperBasisDivideBits.nat_height lo).mono (binaryWordWidth_mono (hOrder.trans hHi))
  have hHigh := (GeneralPaperBasisDivideBits.nat_height hi).mono (binaryWordWidth_mono hHi)
  have hX : RationalHeight x (argumentHeight N) := (hLo.add hHigh).mono (by unfold argumentHeight; omega)
  have hLo' := rationalWordWidth_of_height (hLo.mono (show binaryWordWidth N≤argumentHeight N by unfold argumentHeight; omega))
  have hHi' := rationalWordWidth_of_height (hHigh.mono (show binaryWordWidth N≤argumentHeight N by unfold argumentHeight; omega))
  have hX' := rationalWordWidth_of_height hX
  have hAdd := GeneralPaperScoreBitPrimitive.additionPrice_le model (lo:ℚ) hi _ hLo' hHi' hX'
  have hx : 0≤x := by dsimp only [x]; positivity
  have hN : (N:ℚ)<(2:ℚ)^depth := by exact_mod_cast hSize
  have hBound : (lo:ℚ)+(hi:ℚ)≤2*(N:ℚ) := by exact_mod_cast (show lo+hi≤2*N by omega)
  have hc : x<(2:ℚ)*(2:ℚ)^depth := by dsimp only [x]; linarith only [hN,hBound]
  have hTwo : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hPeak := GeneralPaperQuotientConstructionStorage.bounded model W x 2 (by norm_num) depth (argumentHeight N) 2 hx hc hX hTwo
  have hRecord := record_bound W x 2 (by norm_num) depth (argumentHeight N) 2 hx hc hX hTwo
  change record W result≤_ at hRecord
  have hBounds := GeneralPaperRankMidpoint.midpoint_bounds N depth lo hi hOrder hHi hSize
  have hQ : result.quotient≤N := by dsimp only [result]; omega
  have hWork : result.work=12*depth+2 := GeneralPaperRankMidpoint.midpoint_work depth lo hi
  have hScaled : result.work*W=(12*depth+2)*W := congrArg (·*W) hWork
  have hf := fields_bound W (natBits (metadataCap W depth N))
    [depth,lo,hi,lo+hi,result.quotient,result.work,result.work*W] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap W depth N)+W)+32*W at hf
  change peak model W x 2 depth+record W result+
    rationalWordWidth (lo:ℚ)+rationalWordWidth (hi:ℚ)+rationalWordWidth x+
    GeneralPaperScoreBitPrimitive.additionPrice model (lo:ℚ) hi+
    fields W [depth,lo,hi,lo+hi,result.quotient,result.work,result.work*W]+256*W≤_
  dsimp only [profile]
  omega

end Blotto.GeneralPaperRankMidpointStorage
