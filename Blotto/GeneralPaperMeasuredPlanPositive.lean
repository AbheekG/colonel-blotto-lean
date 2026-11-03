import Blotto.GeneralPaperEqualMeasuredLayout

/-! Nonempty measured blocks. Empty datatype payloads generate no blocks;
actual reference/header blocks are positive at a positive reference width.
The block count is therefore bounded by the actual measured bit extent. -/
namespace Blotto.GeneralPaperMeasuredPlanPositive
open GeneralPaperMeasuredBlockPlan
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def Positive (p : Plan) : Prop := ∀ size ∈ p.sizes,0 < size

theorem natural (model : RationalCostModel) (S n : ℕ) : Positive (GeneralPaperMeasuredBlockPlan.natural model S n) := by
  intro size h
  rw [natural_data] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  subst size
  unfold GeneralPaperEncodedScalarStorage.natBits
  omega

theorem rational (model : RationalCostModel) (S : ℕ) (q : ℚ) : Positive (GeneralPaperMeasuredBlockPlan.rational model S q) := by
  intro size h
  rw [rational_data] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  subst size
  have h := GeneralPaperEqualNativeDrawRepresentation.budget_width q
  omega

theorem references (model : RationalCostModel) (S A count stride fixed : ℕ)
    (hA : 0 < A) (hHeader : 0 < stride * count + fixed) :
    Positive (GeneralPaperMeasuredBlockPlan.references model S A count stride fixed) := by
  intro size h
  rw [references_data] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  subst size
  exact Nat.mul_pos hA hHeader

theorem join (S : ℕ) (left right : Plan) (hl : Positive left) (hr : Positive right) :
    Positive (GeneralPaperMeasuredBlockPlan.join S left right) := by
  intro size h
  rw [join_data] at h
  rcases List.mem_append.mp h with h | h
  · exact hl size h
  · exact hr size h

theorem sequence (S : ℕ) (plans : List Plan) (hPlans : ∀ p ∈ plans,Positive p) :
    Positive (GeneralPaperMeasuredBlockPlan.sequence S plans) := by
  intro size h
  rw [sequence_data] at h
  obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hSizes
  exact hPlans p hp size hSize

theorem array {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) (hA : 0 < A) (hMeasure : ∀ j,Positive (measure (source.read j))) :
    Positive (GeneralPaperMeasuredArrayBlockPlan.array model S A measure source) := by
  intro size h
  rw [GeneralPaperMeasuredArrayBlockPlan.array_data] at h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | h
  · exact Nat.mul_pos hA (by omega)
  · obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hSizes
    exact hMeasure j size hSize

theorem list {α : Type*} (model : RationalCostModel) (S A stride fixed : ℕ) (measure : α → Plan)
    (xs : List α) (hA : 0 < A) (hHeader : 0 < stride * xs.length + fixed)
    (hMeasure : ∀ x ∈ xs,Positive (measure x)) :
    Positive (GeneralPaperMeasuredListBlockPlan.run model S A stride fixed measure xs) := by
  intro size h
  rw [GeneralPaperMeasuredListBlockPlan.data] at h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | h
  · exact Nat.mul_pos hA hHeader
  · obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp h
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hSizes
    exact hMeasure x hx size hSize

theorem length_le_sum (xs : List ℕ) (h : ∀ size ∈ xs,0 < size) : xs.length ≤ xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.length_cons,List.sum_cons]
    omega

theorem block_count (p : Plan) (h : Positive p) : p.sizes.length ≤ p.sizes.sum := length_le_sum p.sizes h

end Blotto.GeneralPaperMeasuredPlanPositive
