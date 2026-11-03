import Blotto.GeneralPaperSignedCutPrice

/-! Complete signed-tail preparation reuses the two generated cut arrays
and the two generated rank caches. All four native annotation additions
are charged in place; the two signs retain one common summary/normalizer.
-/
namespace Blotto.GeneralPaperSignedTailExecution
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (queries : FixedArrayTable m ℕ) : GeneralPaperSignedTailPlan.Plan k m × ℕ :=
  let pc := GeneralPaperSignedCutExecution.run bits index primitive W U false queries
  let nc := GeneralPaperSignedCutExecution.run bits index primitive W U true queries
  let pr := GeneralPaperRankArrayExecution.prepare bits index primitive W k summary pc.1.1
  let nr := GeneralPaperRankArrayExecution.prepare bits index primitive W k summary nc.1.1
  let cutWork := pc.1.2+nc.1.2
  let posWork := cutWork+pr.1.2
  let negWork := posWork+nr.1.2
  (⟨pr.1.1,nr.1.1,negWork+16⟩,pc.2+nc.2+pr.2+nr.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) pc.1.2 nc.1.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) cutWork pr.1.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) posWork nr.1.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) negWork 16+128*W)

theorem data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (queries : FixedArrayTable m ℕ) :
    (run bits index primitive W k U summary queries).1=GeneralPaperSignedTailPlan.prepare k U summary queries := by
  unfold run GeneralPaperSignedTailPlan.prepare
  dsimp only
  simp only [GeneralPaperSignedCutExecution.data,GeneralPaperRankArrayData.prepare_data]

theorem positive_count {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (preparedPrefix : Prefix k) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperSignedTailPlan.evaluate k preparedPrefix (run bits index primitive W k U summary queries).1 q).positive=
      GeneralPaperRankedInterval.referenceCount k summary preparedPrefix (queries.read q) U := by
  rw [data]
  exact GeneralPaperSignedTailPlan.evaluate_positive k U summary preparedPrefix queries q

theorem negative_count {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (preparedPrefix : Prefix k) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperSignedTailPlan.evaluate k preparedPrefix (run bits index primitive W k U summary queries).1 q).negative=
      GeneralPaperRankedInterval.referenceCount k summary preparedPrefix (U+queries.read q) (2*U) := by
  rw [data]
  exact GeneralPaperSignedTailPlan.evaluate_negative k U summary preparedPrefix queries q

end Blotto.GeneralPaperSignedTailExecution
