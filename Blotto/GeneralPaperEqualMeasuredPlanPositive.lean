import Blotto.GeneralPaperMeasuredPlanPositive

/-! Every actual retained-field plan has positive blocks at its stored
reference width. Unit/absent payloads create no blocks, and all descriptor
headers have positive fixed arity. No extra native size premise is needed. -/
namespace Blotto.GeneralPaperEqualMeasuredPlanPositive
open GeneralPaperMeasuredPlanPositive (Positive)
open GeneralPaperMeasuredBlockPlan
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem empty (S : ℕ) : Positive (GeneralPaperEqualMeasuredLeafPlans.empty S) := by
  intro size h
  cases h

theorem tag (S : ℕ) : Positive (GeneralPaperEqualMeasuredLeafPlans.tag S) := by
  intro size h
  simp only [GeneralPaperEqualMeasuredLeafPlans.tag,List.mem_cons,List.not_mem_nil,or_false] at h
  subst size
  decide

theorem reserve (model : RationalCostModel) (S A arity : ℕ) (hA : 0 < A) (hArity : 0 < arity) :
    Positive (GeneralPaperEqualMeasuredLeafPlans.reserve model S A arity) :=
  GeneralPaperMeasuredPlanPositive.references model S A 0 0 arity hA (by omega)

theorem route {m : ℕ} (model : RationalCostModel) (S A : ℕ) (x : GroupRoute m) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredLeafPlans.route model S A x) := by
  dsimp only [GeneralPaperEqualMeasuredLeafPlans.route]
  apply GeneralPaperMeasuredPlanPositive.sequence
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact tag S
  · cases x.1 with
    | none => exact empty S
    | some g => exact GeneralPaperMeasuredPlanPositive.natural model S g.val
  · exact GeneralPaperMeasuredPlanPositive.rational model S x.2
  · exact reserve model S A 16 hA (by decide)

theorem word {w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedBinaryWord w) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredLeafPlans.word model S A x) := by
  apply GeneralPaperMeasuredPlanPositive.join
  · exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ x.bits hA (by omega) (fun _ _ => tag S)
  · exact reserve model S A 16 hA (by decide)

theorem row {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : Fin r × FixedBinaryWord w) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredLeafPlans.row model S A x) := by
  apply GeneralPaperMeasuredPlanPositive.sequence
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl
  · exact GeneralPaperMeasuredPlanPositive.natural model S x.1.val
  · exact word model S A x.2 hA
  · exact reserve model S A 16 hA (by decide)

theorem matrix {m r : ℕ} (model : RationalCostModel) (S A : ℕ)
    (x : FixedArrayTable r (FixedArrayTable m ℚ)) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A x) := by
  apply GeneralPaperMeasuredPlanPositive.array model S A _ x hA
  intro i
  exact GeneralPaperMeasuredPlanPositive.array model S A _ (x.read i) hA
    (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)

theorem segments {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (x : PreparedSegmentDescriptor l) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredRetainedPlan.segments model S A x) := by
  apply GeneralPaperMeasuredPlanPositive.sequence
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact GeneralPaperMeasuredPlanPositive.array model S A _ x.weights hA
      (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
  · exact matrix model S A x.left hA
  · exact matrix model S A x.right hA
  · exact reserve model S A 32 hA (by decide)

theorem prepared {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualPreparedCache.Prepared G l) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A x) := by
  apply GeneralPaperMeasuredPlanPositive.sequence
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
  · exact GeneralPaperMeasuredPlanPositive.array model S A _ x.routes.table hA (fun j => route model S A _ hA)
  · exact segments model S A x.segments hA
  · exact GeneralPaperMeasuredPlanPositive.array model S A _ x.counts hA
      (fun j => GeneralPaperMeasuredPlanPositive.natural model S _)
  · exact GeneralPaperMeasuredPlanPositive.list model S A 1 32 _ _ hA (by omega)
      (fun n _ => GeneralPaperMeasuredPlanPositive.natural model S n)
  · exact GeneralPaperMeasuredPlanPositive.rational model S x.budget
  · exact reserve model S A 64 hA (by decide)

theorem boolean {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (x : GeneralPaperEqualBooleanCache.Cache p) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A x) := by
  apply GeneralPaperMeasuredPlanPositive.sequence
  intro plan hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact word model S A x.denominator hA
  · exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ x.rows hA (by omega)
      (fun x _ => row model S A x hA)
  · exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ x.ruler hA (by omega) (fun _ _ => empty S)
  · exact reserve model S A 64 hA (by decide)

theorem sampler {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualStoredBitSampler.Sampler G l) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A x) := by
  apply GeneralPaperMeasuredPlanPositive.sequence
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact prepared model S A x.prepared hA
  · exact boolean model S A x.categorical hA
  · exact GeneralPaperMeasuredPlanPositive.list model S A 1 32 _ _ hA (by omega)
      (fun n _ => GeneralPaperMeasuredPlanPositive.natural model S n)
  · exact reserve model S A 64 hA (by decide)

theorem branch {n : ℕ} (model : RationalCostModel) (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (x : GeneralPaperEqualBitBranch.Prepared v k budget) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredSelectedPlan.branch model S A x) := by
  cases x with
  | dominant chosen heavy source correct =>
    apply GeneralPaperMeasuredPlanPositive.sequence
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact GeneralPaperMeasuredPlanPositive.array model S A _ _ hA
        (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
    · exact GeneralPaperMeasuredPlanPositive.natural model S chosen.val
    · exact reserve model S A 32 hA (by decide)
  | grouped small source hK hB =>
    have h : 0 < source.address := by rw [source.address_correct]; exact binaryWordWidth_pos _
    exact sampler model S source.address source h

theorem header (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    Positive (GeneralPaperEqualMeasuredSelectedPlan.header model S A) := by
  apply GeneralPaperMeasuredPlanPositive.join
  · exact GeneralPaperMeasuredPlanPositive.list model S A 1 32 _ _ hA (by omega)
      (fun n _ => GeneralPaperMeasuredPlanPositive.natural model S n)
  · exact reserve model S A 64 hA (by decide)

theorem selected {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : GeneralPaperEqualSelectedSampler.Sampler v k budget) :
    Positive (GeneralPaperEqualMeasuredSelectedPlan.run model S a) := by
  have hA : 0 < a.address := (GeneralPaperEqualMeasuredLayout.widths_positive a).2
  exact GeneralPaperMeasuredPlanPositive.join S _ _ (branch model S a.address a.branch hA) (header model S a.address hA)

end Blotto.GeneralPaperEqualMeasuredPlanPositive
