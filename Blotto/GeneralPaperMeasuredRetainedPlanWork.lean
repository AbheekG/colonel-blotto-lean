import Blotto.GeneralPaperMeasuredListPlanWork

/-! Complete actual retained-sampler size-plan work. Fixed datatype depth
gives one universal constant times measured extent and metadata, uniformly
over all dimensions, values, cache fields and original budgets. No sampler
is recomputed and no payload is replaced by a worst-case scalar size. -/
namespace Blotto.GeneralPaperMeasuredRetainedPlanWork
open GeneralPaperMeasuredBlockPlan GeneralPaperMeasuredPlanWorkAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem route {m : ℕ} (model : RationalCostModel) (S A : ℕ) (x : GroupRoute m) (hA : 0 < A) :
    Good model S A 13 (GeneralPaperEqualMeasuredLeafPlans.route model S A x) := by
  dsimp only [GeneralPaperEqualMeasuredLeafPlans.route]
  apply sequence_work model S A 1 _ hA
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact GeneralPaperMeasuredLeafPlanWork.tag model S A
  · cases x.1 with
    | none => exact GeneralPaperMeasuredLeafPlanWork.empty model S A
    | some g => exact GeneralPaperMeasuredLeafPlanWork.natural model S A g.val hA
  · exact GeneralPaperMeasuredLeafPlanWork.rational model S A x.2 hA
  · exact GeneralPaperMeasuredLeafPlanWork.reserve model S A 16 hA (by decide) (by decide)

theorem word {w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedBinaryWord w) (hA : 0 < A) :
    Good model S A 12 (GeneralPaperEqualMeasuredLeafPlans.word model S A x) := by
  apply join_work model S A 9 1 _ _ hA
  · exact GeneralPaperMeasuredListPlanWork.list model S A 1 2 32 _ x.bits hA (by decide) (by decide) (by decide) (by decide)
      (fun _ _ => GeneralPaperMeasuredLeafPlanWork.tag model S A)
  · exact GeneralPaperMeasuredLeafPlanWork.reserve model S A 16 hA (by decide) (by decide)

theorem row {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : Fin r × FixedBinaryWord w) (hA : 0 < A) :
    Good model S A 43 (GeneralPaperEqualMeasuredLeafPlans.row model S A x) := by
  apply sequence_work model S A 12 _ hA
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl
  · exact mono model S A 1 12 _ (GeneralPaperMeasuredLeafPlanWork.natural model S A x.1.val hA) (by decide)
  · exact word model S A x.2 hA
  · exact mono model S A 1 12 _ (GeneralPaperMeasuredLeafPlanWork.reserve model S A 16 hA (by decide) (by decide)) (by decide)

theorem matrix {m r : ℕ} (model : RationalCostModel) (S A : ℕ)
    (x : FixedArrayTable r (FixedArrayTable m ℚ)) (hA : 0 < A) :
    Good model S A 17 (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A x) := by
  apply GeneralPaperMeasuredArrayPlanWork.array model S A 9 _ x hA
  intro i
  exact GeneralPaperMeasuredArrayPlanWork.array model S A 1 _ (x.read i) hA
    (fun j => GeneralPaperMeasuredLeafPlanWork.rational model S A ((x.read i).read j) hA)

theorem segments {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (x : PreparedSegmentDescriptor l) (hA : 0 < A) :
    Good model S A 77 (GeneralPaperEqualMeasuredRetainedPlan.segments model S A x) := by
  apply sequence_work model S A 17 _ hA
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · apply mono model S A 9 17
    · exact GeneralPaperMeasuredArrayPlanWork.array model S A 1 _ x.weights hA
        (fun j => GeneralPaperMeasuredLeafPlanWork.rational model S A (x.weights.read j) hA)
    · decide
  · exact matrix model S A x.left hA
  · exact matrix model S A x.right hA
  · exact mono model S A 1 17 _ (GeneralPaperMeasuredLeafPlanWork.reserve model S A 32 hA (by decide) (by decide)) (by decide)

theorem prepared {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualPreparedCache.Prepared G l) (hA : 0 < A) :
    Good model S A 475 (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A x) := by
  apply sequence_work model S A 77 _ hA
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
  · apply mono model S A 21 77
    · exact GeneralPaperMeasuredArrayPlanWork.array model S A 13 _ x.routes.table hA (fun j => route model S A (x.routes.table.read j) hA)
    · decide
  · exact mono model S A 77 77 _ (segments model S A x.segments hA) (by decide)
  · apply mono model S A 9 77
    · exact GeneralPaperMeasuredArrayPlanWork.array model S A 1 _ x.counts hA (fun j => GeneralPaperMeasuredLeafPlanWork.natural model S A (x.counts.read j) hA)
    · decide
  · apply mono model S A 9 77
    · exact GeneralPaperMeasuredListPlanWork.list model S A 1 1 32 _ _ hA (by decide) (by decide) (by decide) (by decide)
        (fun value _ => GeneralPaperMeasuredLeafPlanWork.natural model S A value hA)
    · decide
  · exact mono model S A 1 77 _ (GeneralPaperMeasuredLeafPlanWork.rational model S A x.budget hA) (by decide)
  · exact mono model S A 1 77 _ (GeneralPaperMeasuredLeafPlanWork.reserve model S A 64 hA (by decide) (by decide)) (by decide)

theorem boolean {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (x : GeneralPaperEqualBooleanCache.Cache p) (hA : 0 < A) :
    Good model S A 213 (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A x) := by
  apply sequence_work model S A 51 _ hA
  intro plan hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact mono model S A 12 51 _ (word model S A x.denominator hA) (by decide)
  · exact GeneralPaperMeasuredListPlanWork.list model S A 43 2 32 _ x.rows hA (by decide) (by decide) (by decide) (by decide)
      (fun value _ => row model S A value hA)
  · apply mono model S A 9 51
    · exact GeneralPaperMeasuredListPlanWork.list model S A 1 2 32 _ x.ruler hA (by decide) (by decide) (by decide) (by decide)
        (fun _ _ => GeneralPaperMeasuredLeafPlanWork.empty model S A)
    · decide
  · exact mono model S A 1 51 _ (GeneralPaperMeasuredLeafPlanWork.reserve model S A 64 hA (by decide) (by decide)) (by decide)

theorem sampler {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualStoredBitSampler.Sampler G l) (hA : 0 < A) :
    Good model S A 1909 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A x) := by
  apply sequence_work model S A 475 _ hA
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact prepared model S A x.prepared hA
  · exact mono model S A 213 475 _ (boolean model S A x.categorical hA) (by decide)
  · apply mono model S A 9 475
    · exact GeneralPaperMeasuredListPlanWork.list model S A 1 1 32 _ _ hA (by decide) (by decide) (by decide) (by decide)
        (fun value _ => GeneralPaperMeasuredLeafPlanWork.natural model S A value hA)
    · decide
  · exact mono model S A 1 475 _ (GeneralPaperMeasuredLeafPlanWork.reserve model S A 64 hA (by decide) (by decide)) (by decide)

theorem header (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    Good model S A 12 (GeneralPaperEqualMeasuredSelectedPlan.header model S A) := by
  apply join_work model S A 9 1 _ _ hA
  · exact GeneralPaperMeasuredListPlanWork.list model S A 1 1 32 _ [A] hA (by decide) (by decide) (by decide) (by decide)
      (fun value _ => GeneralPaperMeasuredLeafPlanWork.natural model S A value hA)
  · exact GeneralPaperMeasuredLeafPlanWork.reserve model S A 64 hA (by decide) (by decide)

theorem dominant {n : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedArrayTable n ℚ) (chosen : Fin n) (hA : 0 < A) :
    Good model S A 34 (sequence S [GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) x,
      GeneralPaperMeasuredBlockPlan.natural model S chosen.val,GeneralPaperEqualMeasuredLeafPlans.reserve model S A 32]) := by
  apply sequence_work model S A 9 _ hA
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl
  · exact GeneralPaperMeasuredArrayPlanWork.array model S A 1 _ x hA (fun j => GeneralPaperMeasuredLeafPlanWork.rational model S A (x.read j) hA)
  · exact mono model S A 1 9 _ (GeneralPaperMeasuredLeafPlanWork.natural model S A chosen.val hA) (by decide)
  · exact mono model S A 1 9 _ (GeneralPaperMeasuredLeafPlanWork.reserve model S A 32 hA (by decide) (by decide)) (by decide)

end Blotto.GeneralPaperMeasuredRetainedPlanWork
