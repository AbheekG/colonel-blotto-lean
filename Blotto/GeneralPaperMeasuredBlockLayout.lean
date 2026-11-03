import Blotto.GeneralPaperEqualMeasuredSelectedPlan

/-! Actual measured sizes feed the executed sequential layout. The returned
regions preserve block order and exact sizes; cursor/encoded-reference and
disjointness proofs use the actual plan total, not a supplied size oracle. -/
namespace Blotto.GeneralPaperMeasuredBlockLayout
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def run (model : RationalCostModel) (S A start : ℕ) (plan : Plan) : List (Region A) × (ℕ × ℕ) :=
  let actual := GeneralPaperSequentialLayout.run model S A start plan.sizes
  (actual.1,actual.2.1,plan.work + actual.2.2 + 64 * (S + A + 1))

theorem cursor (model : RationalCostModel) (S A start : ℕ) (plan : Plan) :
    (run model S A start plan).2.1 = start + plan.sizes.sum := GeneralPaperSequentialLayout.cursor model S A start plan.sizes

theorem lengths (model : RationalCostModel) (S A start : ℕ) (plan : Plan) :
    (run model S A start plan).1.map Region.length = plan.sizes := GeneralPaperSequentialLayout.lengths model S A start plan.sizes

theorem count (model : RationalCostModel) (S A start : ℕ) (plan : Plan) :
    (run model S A start plan).1.length = plan.sizes.length := GeneralPaperSequentialLayout.count model S A start plan.sizes

theorem range (model : RationalCostModel) (S A start : ℕ) (plan : Plan) :
    ∀ r ∈ (run model S A start plan).1,start ≤ r.start ∧ r.stop ≤ start + plan.sizes.sum :=
  GeneralPaperSequentialLayout.range model S A start plan.sizes

theorem disjoint (model : RationalCostModel) (S A start : ℕ) (plan : Plan) :
    List.Pairwise (fun r s : Region A => Disjoint (Set.Ico r.start r.stop) (Set.Ico s.start s.stop))
      (run model S A start plan).1 := GeneralPaperSequentialLayout.disjoint model S A start plan.sizes

theorem references (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ r ∈ (run model S A start plan).1,r.reference.value = r.start :=
  GeneralPaperSequentialLayout.references model S A start plan.sizes hCap

theorem reference_width (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ r ∈ (run model S A start plan).1,binaryWordWidth r.start ≤ A :=
  GeneralPaperSequentialLayout.reference_width model S A start plan.sizes hA hCap

theorem work (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (run model S A start plan).2.2 ≤ plan.work + (plan.sizes.length + 1) * stepPrice model S A + 64 * (S + A + 1) := by
  have h := GeneralPaperSequentialLayout.work model S A start plan.sizes hA hCap
  dsimp only [run]
  omega

theorem lookup_length (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (index : ℕ) :
    ((run model S A start plan).1[index]?).map Region.length = plan.sizes[index]? := by
  have h := congrArg (fun xs : List ℕ => xs[index]?) (lengths model S A start plan)
  simpa only [List.getElem?_map] using h

theorem lookup_start_raw (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ)
    (index : ℕ) (hIndex : index < sizes.length) :
    ((GeneralPaperSequentialLayout.run model S A start sizes).1[index]?).map Region.start =
      some (start + (sizes.take index).sum) := by
  induction sizes generalizing start index with
  | nil => simp only [List.length_nil] at hIndex; omega
  | cons size sizes ih =>
    cases index with
    | zero => simp only [GeneralPaperSequentialLayout.run,List.getElem?_cons_zero,Option.map_some,List.take_zero,List.sum_nil,Nat.add_zero]
    | succ index =>
      have hLength : index + 1 < sizes.length + 1 := hIndex
      have hTail : index < sizes.length := by omega
      have h := ih (start + size) index hTail
      simpa only [GeneralPaperSequentialLayout.run,List.getElem?_cons_succ,List.take_succ_cons,List.sum_cons,Nat.add_assoc] using h

theorem lookup_start (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (index : ℕ) (hIndex : index < plan.sizes.length) :
    ((run model S A start plan).1[index]?).map Region.start = some (start + (plan.sizes.take index).sum) :=
  lookup_start_raw model S A start plan.sizes index hIndex

end Blotto.GeneralPaperMeasuredBlockLayout
