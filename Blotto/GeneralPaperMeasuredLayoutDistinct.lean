import Blotto.GeneralPaperEqualMeasuredPlanPositive

/-! Positive measured blocks have distinct start/reference values. The
same capacity bound limits each measured size word and hence the temporary
plan/region metadata, without charging full payload precision per block. -/
namespace Blotto.GeneralPaperMeasuredLayoutDistinct
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanPositive (Positive)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem starts_raw (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ)
    (hPos : ∀ size ∈ sizes,0 < size) :
    ((GeneralPaperSequentialLayout.run model S A start sizes).1.map Region.start).Nodup := by
  induction sizes generalizing start with
  | nil => exact List.nodup_nil
  | cons size sizes ih =>
    have hSize := hPos size (List.mem_cons_self ..)
    have hTail := ih (start + size) (fun x hx => hPos x (List.mem_cons_of_mem size hx))
    dsimp only [GeneralPaperSequentialLayout.run]
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,hTail⟩
    intro hMem
    obtain ⟨r,hr,hEq⟩ := List.mem_map.mp hMem
    have hRange := GeneralPaperSequentialLayout.range model S A (start + size) sizes r hr
    omega

theorem starts (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (hPos : Positive plan) :
    ((GeneralPaperMeasuredBlockLayout.run model S A start plan).1.map Region.start).Nodup :=
  starts_raw model S A start plan.sizes hPos

theorem reference_values (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hPos : Positive plan) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ((GeneralPaperMeasuredBlockLayout.run model S A start plan).1.map (fun r => r.reference.value)).Nodup := by
  have hEq : (GeneralPaperMeasuredBlockLayout.run model S A start plan).1.map (fun r => r.reference.value) =
      (GeneralPaperMeasuredBlockLayout.run model S A start plan).1.map Region.start :=
    List.map_congr_left (GeneralPaperMeasuredBlockLayout.references model S A start plan hCap)
  rw [hEq]
  exact starts model S A start plan hPos

theorem region_positive (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (hPos : Positive plan) :
    ∀ r ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1,0 < r.length := by
  intro r hr
  apply hPos
  rw [← GeneralPaperMeasuredBlockLayout.lengths model S A start plan]
  exact List.mem_map.mpr ⟨r,hr,rfl⟩

theorem count_le_extent (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (hPos : Positive plan) :
    (GeneralPaperMeasuredBlockLayout.run model S A start plan).1.length ≤ plan.sizes.sum := by
  rw [GeneralPaperMeasuredBlockLayout.count]
  exact GeneralPaperMeasuredPlanPositive.block_count plan hPos

theorem member_le_sum (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.sum_cons]; omega
    · have h := ih hx
      simp only [List.sum_cons]
      omega

theorem size_word (A start : ℕ) (plan : Plan) (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ size ∈ plan.sizes,natBits size ≤ A + 1 := by
  intro size hSize
  have h := member_le_sum plan.sizes size hSize
  have hw := binaryWordWidth_le_of_lt_pow hA (by omega : size < 2 ^ A)
  unfold natBits
  omega

theorem plan_metadata (S A start : ℕ) (plan : Plan) (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    listFootprint S natBits plan.sizes ≤ plan.sizes.length * (A + 1 + 2 * S) + 32 * S :=
  list_bound S (A + 1) natBits plan.sizes (size_word A start plan hA hCap)

def regionFoot {A : ℕ} (S : ℕ) (r : Region A) : ℕ := fields S [r.start,r.length] + A + 64 * S
def regionProfile (S A : ℕ) : ℕ := 3 * A + 2 + 98 * S

theorem region_metadata (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ r ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1,regionFoot S r ≤ regionProfile S A := by
  intro r hr
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan r hr
  have hStart := GeneralPaperMeasuredBlockLayout.reference_width model S A start plan hA hCap r hr
  have hLength := binaryWordWidth_le_of_lt_pow hA (by unfold Region.stop at hRange; omega : r.length < 2 ^ A)
  have hf := fields_bound S (A + 1) [r.start,r.length] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> unfold natBits <;> omega)
  change fields S _ ≤ 2 * (A + 1 + S) + 32 * S at hf
  unfold regionFoot regionProfile
  omega

theorem layout_metadata (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    listFootprint S (regionFoot S) (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 ≤
      plan.sizes.length * (regionProfile S A + 2 * S) + 32 * S := by
  have h := list_bound S (regionProfile S A) (regionFoot S)
    (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 (region_metadata model S A start plan hA hCap)
  rw [GeneralPaperMeasuredBlockLayout.count] at h
  exact h

end Blotto.GeneralPaperMeasuredLayoutDistinct
