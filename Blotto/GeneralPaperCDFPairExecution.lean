import Blotto.GeneralPaperFieldPlanCounters

/-! Strict and weak CDF ranks from two native shifted cut arrays. Every
native annotation addition is charged in place; both ranks share the
retained summary and no annotation-sum pass follows either array fill.
-/
namespace Blotto.GeneralPaperCDFPairExecution
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    GeneralPaperCDFPairPlan.Plan k m × ℕ :=
  let lc := GeneralPaperCDFShiftPrice.run bits index price W 0 queries
  let uc := GeneralPaperCDFShiftPrice.run bits index price W 1 queries
  let lr := GeneralPaperRankArrayExecution.prepare bits index price W k summary lc.1.1
  let ur := GeneralPaperRankArrayExecution.prepare bits index price W k summary uc.1.1
  (⟨lr.1.1,ur.1.1,lc.1.2+uc.1.2+lr.1.2+ur.1.2+16⟩,
    lc.2+uc.2+lr.2+ur.2+GeneralPaperSignedTailOperands.additions price lc.1.2 uc.1.2 lr.1.2 ur.1.2+128*W)

theorem data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run bits index price W k summary queries).1=GeneralPaperCDFPairPlan.prepare k summary queries := by
  unfold run GeneralPaperCDFPairPlan.prepare
  dsimp only
  simp only [GeneralPaperCDFShiftPrice.data,GeneralPaperRankArrayData.prepare_data]

theorem lower_count {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k : ℕ) (summary : Summary k)
    (preparedPrefix : Prefix k) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperCDFPairPlan.evaluate k preparedPrefix (run bits index price W k summary queries).1 q).lower=
      GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (queries.read q) := by
  rw [data]
  exact GeneralPaperCDFPairPlan.evaluate_lower k summary preparedPrefix queries q

theorem upper_count {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k : ℕ) (summary : Summary k)
    (preparedPrefix : Prefix k) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperCDFPairPlan.evaluate k preparedPrefix (run bits index price W k summary queries).1 q).upper=
      GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (queries.read q+1) := by
  rw [data]
  exact GeneralPaperCDFPairPlan.evaluate_upper k summary preparedPrefix queries q

end Blotto.GeneralPaperCDFPairExecution
