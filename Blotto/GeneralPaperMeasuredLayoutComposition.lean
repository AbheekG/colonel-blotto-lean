import Blotto.GeneralPaperScalarArrayReferenceProgram

/-! The executed sequential layout respects concatenated field plans.
This identifies a component's actual regions inside the complete allocation
without rerunning the component layout during installation. -/
namespace Blotto.GeneralPaperMeasuredLayoutComposition
open GeneralPaperSequentialLayout GeneralPaperMeasuredBlockPlan
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem regions_append (model : RationalCostModel) (S A start : ℕ) (first second : List ℕ) :
    (GeneralPaperSequentialLayout.run model S A start (first ++ second)).1 =
      (GeneralPaperSequentialLayout.run model S A start first).1 ++
      (GeneralPaperSequentialLayout.run model S A
        (GeneralPaperSequentialLayout.run model S A start first).2.1 second).1 := by
  induction first generalizing start with
  | nil => rfl
  | cons size sizes ih =>
    simp only [List.cons_append,GeneralPaperSequentialLayout.run,ih,List.cons_append]

theorem joined_regions (model : RationalCostModel) (S A start : ℕ) (first second : Plan) :
    (GeneralPaperMeasuredBlockLayout.run model S A start (join S first second)).1 =
      (GeneralPaperMeasuredBlockLayout.run model S A start first).1 ++
      (GeneralPaperMeasuredBlockLayout.run model S A
        (GeneralPaperMeasuredBlockLayout.run model S A start first).2.1 second).1 := by
  change (GeneralPaperSequentialLayout.run model S A start (join S first second).sizes).1 = _
  rw [join_data]
  exact regions_append model S A start first.sizes second.sizes

theorem first_regions (model : RationalCostModel) (S A start : ℕ) (first second : List ℕ) :
    ((GeneralPaperSequentialLayout.run model S A start (first ++ second)).1.take first.length) =
      (GeneralPaperSequentialLayout.run model S A start first).1 := by
  rw [regions_append,← GeneralPaperSequentialLayout.count model S A start first,List.take_left]

end Blotto.GeneralPaperMeasuredLayoutComposition
