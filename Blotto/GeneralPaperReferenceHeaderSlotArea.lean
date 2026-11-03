import Blotto.GeneralPaperEqualMixedReferenceInstallation

/-! Reference-slot work is charged to actual allocated header area. Valid
headers selected in layout order cannot duplicate ownership. Native inner and
outer slot areas together fit the complete selected description, retaining
one additive original-budget payload rather than expanding it per field. -/
namespace Blotto.GeneralPaperReferenceHeaderSlotArea
open GeneralPaperReferenceRegionSlots GeneralPaperReferenceLayoutInstallation GeneralPaperSequentialLayout GeneralPaperMeasuredBlockPlan
open GeneralPaperEqualMeasuredLayout GeneralPaperEqualSelectedSampler
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def slots {A : ℕ} (headers : List (Header A)) : ℕ := (headers.map (fun header => header.targets.length)).sum

theorem sum_sublist (xs ys : List ℕ) (hSub : xs.Sublist ys) : xs.sum ≤ ys.sum := by
  induction hSub with
  | slnil => exact le_refl _
  | cons x h ih => simp only [List.sum_cons]; omega
  | cons_cons x h ih => simp only [List.sum_cons]; omega

theorem owner_area (A : ℕ) (headers : List (Header A)) (hValid : ∀ header ∈ headers,Valid header) :
    A * slots headers ≤ (headers.map (fun header => header.region.length)).sum := by
  induction headers with
  | nil => simp only [slots,List.map_nil,List.sum_nil,Nat.mul_zero,le_refl]
  | cons header headers ih =>
    have hh := hValid header (List.mem_cons_self ..)
    have ht := ih (fun h hm => hValid h (List.mem_cons_of_mem header hm))
    have he := Nat.mul_le_mul_left A (show header.targets.length ≤ header.fixed + header.targets.length by omega)
    have hHead : A * header.targets.length ≤ header.region.length := he.trans hh
    change A * (header.targets.length + slots headers) ≤ header.region.length + (headers.map (fun h => h.region.length)).sum
    rw [Nat.mul_add]
    exact Nat.add_le_add hHead ht

theorem layout_area (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) (hValid : ∀ header ∈ headers,Valid header) :
    A * slots headers ≤ plan.sizes.sum := by
  have h := sum_sublist _ _ (hFrom.map Region.length)
  rw [GeneralPaperMeasuredBlockLayout.lengths] at h
  simp only [List.map_map,Function.comp_def] at h
  exact (owner_area A headers hValid).trans h

theorem layout_count (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) (hA : 0 < A) (hValid : ∀ header ∈ headers,Valid header) :
    slots headers ≤ plan.sizes.sum :=
  (Nat.le_mul_of_pos_left (slots headers) hA).trans (layout_area model S A start plan headers hFrom hValid)

theorem native_area {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (hInside : (inside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).inner)
    (hOutside : (outside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hInsideValid : ∀ header ∈ inside,Valid header) (hOutsideValid : ∀ header ∈ outside,Valid header) :
    innerWidth a * slots inside + a.address * slots outside ≤ GeneralPaperEqualSelectedDescription.footprint a := by
  have hi := layout_area model S (innerWidth a) 0 (inner model S a) inside
    (GeneralPaperEqualReferencePoolInstallation.inner_from model S a inside hInside) hInsideValid
  have ho := layout_area model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary (outer model S a) outside
    (GeneralPaperEqualReferencePoolInstallation.outer_from model S a outside hOutside) hOutsideValid
  have hTotal : (inner model S a).sizes.sum + (outer model S a).sizes.sum = GeneralPaperEqualSelectedDescription.footprint a := by
    change (GeneralPaperEqualMeasuredSelectedPlan.branch model S a.address a.branch).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S a.address).sizes.sum = _
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum,GeneralPaperEqualMeasuredSelectedPlan.header_sum]
    rfl
  omega

theorem native_count {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (hInside : (inside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).inner)
    (hOutside : (outside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hInsideValid : ∀ header ∈ inside,Valid header) (hOutsideValid : ∀ header ∈ outside,Valid header) :
    slots inside + slots outside ≤ GeneralPaperEqualSelectedDescription.footprint a := by
  have h := native_area model S a inside outside hInside hOutside hInsideValid hOutsideValid
  have hi := Nat.le_mul_of_pos_left (slots inside) (widths_positive a).1
  have ho := Nat.le_mul_of_pos_left (slots outside) (widths_positive a).2
  omega

end Blotto.GeneralPaperReferenceHeaderSlotArea
