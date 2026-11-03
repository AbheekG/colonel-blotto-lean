import Blotto.GeneralPaperEncodedFixedVector

/-! Retained strict/weak CDF and signed-tail rank plans include their native
work annotations. Constructor bounds are erased evidence, not extra passes. -/
namespace Blotto.GeneralPaperEncodedRankPlans
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def base (k : ℕ) : ℕ := (35+k)*(12*(35+k)+34)+120
def rankWord (k : ℕ) : ℕ := GeneralPaperEncodedFixedVector.rankWord ((GeneralPaperSourceParameters.prepare k).summarySize+1)

def cdfFootprint {k n : ℕ} (W : ℕ) (plan : GeneralPaperCDFPairPlan.Plan k n) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits plan.lower+
    GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits plan.upper+
    (1+binaryWordWidth plan.work)+64*W

def cdfProfile (W n k : ℕ) : ℕ := 2*n*(rankWord k+W)+2*n*base k+90+128*W

theorem cdf {n : ℕ} (W k : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) :
    cdfFootprint W (GeneralPaperCDFPairPlan.prepare k summary queries)≤cdfProfile W n k := by
  have hl := GeneralPaperEncodedFixedVector.rank_array W (GeneralPaperCDFPairPlan.prepare k summary queries).lower
  have hu := GeneralPaperEncodedFixedVector.rank_array W (GeneralPaperCDFPairPlan.prepare k summary queries).upper
  have hw := GeneralPaperEncodedFixedVector.annotation _ _ (GeneralPaperCDFPairPlan.prepare_work k summary queries)
  unfold cdfFootprint cdfProfile rankWord base
  nlinarith only [hl,hu,hw]

def tailFootprint {k n : ℕ} (W : ℕ) (plan : GeneralPaperSignedTailPlan.Plan k n) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits plan.positive+
    GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits plan.negative+
    (1+binaryWordWidth plan.work)+64*W

def tailProfile (W n k : ℕ) : ℕ := 2*(n+1)*(rankWord k+W)+2*(n+1)*base k+90+128*W

theorem tail {n : ℕ} (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) :
    tailFootprint W (GeneralPaperSignedTailPlan.prepare k U summary queries)≤tailProfile W n k := by
  have hp := GeneralPaperEncodedFixedVector.rank_array W (GeneralPaperSignedTailPlan.prepare k U summary queries).positive
  have hn := GeneralPaperEncodedFixedVector.rank_array W (GeneralPaperSignedTailPlan.prepare k U summary queries).negative
  have hw := GeneralPaperEncodedFixedVector.annotation _ _ (GeneralPaperSignedTailPlan.prepare_work k U summary queries)
  unfold tailFootprint tailProfile rankWord base
  nlinarith only [hp,hn,hw]

def lossFootprint {k n : ℕ} (W : ℕ) (plan : GeneralPaperQueryLossCounts.Plan k n) : ℕ :=
  cdfFootprint W plan.cdf+tailFootprint W plan.tails+(1+binaryWordWidth plan.work)+64*W

def lossProfile (W n k : ℕ) : ℕ := cdfProfile W n k+tailProfile W n k+(4*n+2)*base k+194+64*W

theorem loss {n : ℕ} (W k U : ℕ) (cdfSummary tailSummary : Summary k) (queries : FixedArrayTable n ℕ) :
    lossFootprint W (GeneralPaperQueryLossCounts.prepare k U cdfSummary tailSummary queries)≤lossProfile W n k := by
  have hc := cdf W k cdfSummary queries
  have ht := tail W k U tailSummary queries
  have hw := GeneralPaperEncodedFixedVector.annotation _ _ (GeneralPaperQueryLossCounts.prepare_work k U cdfSummary tailSummary queries)
  unfold lossFootprint lossProfile
  change cdfFootprint W (GeneralPaperCDFPairPlan.prepare k cdfSummary queries)+
    tailFootprint W (GeneralPaperSignedTailPlan.prepare k U tailSummary queries)+(1+binaryWordWidth _)+64*W≤_
  change 1+binaryWordWidth _≤(4*n+2)*base k+194 at hw
  omega

theorem cdf_mono (W k n N : ℕ) (hn : n≤N) : cdfProfile W n k≤cdfProfile W N k := by
  have ha := Nat.mul_le_mul_right (rankWord k+W) (Nat.mul_le_mul_left 2 hn)
  have hb := Nat.mul_le_mul_right (base k) (Nat.mul_le_mul_left 2 hn)
  unfold cdfProfile
  omega

theorem tail_mono (W k n N : ℕ) (hn : n≤N) : tailProfile W n k≤tailProfile W N k := by
  have ha := Nat.mul_le_mul_right (rankWord k+W) (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hn 1))
  have hb := Nat.mul_le_mul_right (base k) (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hn 1))
  unfold tailProfile
  omega

theorem loss_mono (W k n N : ℕ) (hn : n≤N) : lossProfile W n k≤lossProfile W N k := by
  have hc := cdf_mono W k n N hn
  have ht := tail_mono W k n N hn
  have hw := Nat.mul_le_mul_right (base k) (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hn) 2)
  unfold lossProfile
  omega

end Blotto.GeneralPaperEncodedRankPlans
