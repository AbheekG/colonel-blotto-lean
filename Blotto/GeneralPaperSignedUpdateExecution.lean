import Blotto.GeneralPaperSignedPositionsPrice

/-! Complete signed-update rank plan: projected positions, weak-CDF cuts
and retained rank array, preserving the native codes/positions/work fields.
-/
namespace Blotto.GeneralPaperSignedUpdateExecution
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable m ℕ) :
    GeneralPaperSignedUpdatePlan.Plan k m × ℕ :=
  let positions := GeneralPaperSignedPositionsPrice.run bits index price W U codes
  let cuts := GeneralPaperCDFShiftPrice.run bits index price W 1 positions.1.1
  let ranks := GeneralPaperRankArrayExecution.prepare bits index price W k summary cuts.1.1
  (⟨codes,positions.1.1,ranks.1.1,positions.1.2+cuts.1.2+ranks.1.2+16⟩,
    positions.2+cuts.2+ranks.2+GeneralPaperFieldPlanCounters.triple price positions.1.2 cuts.1.2 ranks.1.2+128*W)

theorem data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable m ℕ) :
    (run bits index price W k U summary codes).1=GeneralPaperSignedUpdatePlan.prepare k U summary codes := by
  unfold run GeneralPaperSignedUpdatePlan.prepare
  dsimp only
  simp only [GeneralPaperSignedPositionsPrice.data,GeneralPaperCDFShiftPrice.data,GeneralPaperRankArrayData.prepare_data]

theorem count {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U bid : ℕ) (summary : Summary k)
    (preparedPrefix : Prefix k) (codes : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperSignedUpdatePlan.evaluate k U bid preparedPrefix (run bits index price W k U summary codes).1 q).count=
      GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (GeneralPaperSignedUpdatePlan.project U (codes.read q)+1) := by
  rw [data]
  exact GeneralPaperSignedUpdatePlan.evaluate_count k U bid summary preparedPrefix codes q

end Blotto.GeneralPaperSignedUpdateExecution
