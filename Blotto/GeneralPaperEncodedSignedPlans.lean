import Blotto.GeneralPaperEncodedRankPlans

/-! Signed-update plans retain their original codes, projected positions,
finite ranks and native annotation. Projection never increases a code word. -/
namespace Blotto.GeneralPaperEncodedSignedPlans
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {k n : ℕ} (W : ℕ) (plan : GeneralPaperSignedUpdatePlan.Plan k n) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W plan.codes+GeneralPaperEncodedNatArray.footprint W plan.positions+
    GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits plan.ranks+
    (1+binaryWordWidth plan.work)+64*W

def profile (W L n k : ℕ) : ℕ :=
  2*n*(L+W)+n*(GeneralPaperEncodedRankPlans.rankWord k+W)+n*(GeneralPaperEncodedRankPlans.base k+58)+72+160*W

theorem project_le (U code : ℕ) : GeneralPaperSignedUpdatePlan.project U code≤code := by
  unfold GeneralPaperSignedUpdatePlan.project
  split <;> omega

theorem prepared {n : ℕ} (W L k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ)
    (hCodes : ∀ i,1+binaryWordWidth (codes.read i)≤L) :
    footprint W (GeneralPaperSignedUpdatePlan.prepare k U summary codes)≤profile W L n k := by
  have hc := GeneralPaperEncodedNatArray.bounded W L codes hCodes
  have hp := GeneralPaperEncodedNatArray.bounded W L (GeneralPaperSignedUpdatePlan.prepare k U summary codes).positions (by
    intro i
    change 1+binaryWordWidth ((GeneralPaperSignedUpdatePlan.projected U codes).1.read i)≤L
    rw [GeneralPaperSignedUpdatePlan.projected_read]
    exact (Nat.add_le_add_left (binaryWordWidth_mono (project_le U (codes.read i))) 1).trans (hCodes i))
  have hr := GeneralPaperEncodedFixedVector.rank_array W (GeneralPaperSignedUpdatePlan.prepare k U summary codes).ranks
  have hw := GeneralPaperEncodedFixedVector.annotation _ _ (GeneralPaperSignedUpdatePlan.prepare_work k U summary codes)
  change 1+binaryWordWidth _≤n*(GeneralPaperEncodedRankPlans.base k+58)+72 at hw
  change GeneralPaperEncodedNatArray.footprint W codes+GeneralPaperEncodedNatArray.footprint W _+_+_+64*W≤_
  unfold profile GeneralPaperEncodedRankPlans.rankWord
  nlinarith only [hc,hp,hr,hw]

theorem profile_mono (W L k n N : ℕ) (hn : n≤N) : profile W L n k≤profile W L N k := by
  have ha := Nat.mul_le_mul_right (L+W) (Nat.mul_le_mul_left 2 hn)
  have hb := Nat.mul_le_mul_right (GeneralPaperEncodedRankPlans.rankWord k+W) hn
  have hc := Nat.mul_le_mul_right (GeneralPaperEncodedRankPlans.base k+58) hn
  unfold profile
  omega

theorem code_word (lambda x : ℕ) (hx : x≤2^(lambda+1)) :
    1+binaryWordWidth x≤GeneralPaperDecoderControls.operandWidth lambda := by
  have hp := Nat.two_pow_pos (lambda+1)
  have hb : x<2^(lambda+2) := by rw [show lambda+2=(lambda+1)+1 by omega,pow_succ]; omega
  have hw := GeneralPaperCFOperandPrice.small_word (lambda+2) x hb
  unfold GeneralPaperDecoderControls.operandWidth
  omega

end Blotto.GeneralPaperEncodedSignedPlans
