import Blotto.GeneralPaperEqualOuterFieldLayout

/-! A priced single traversal selects the last actual allocated region.
It neither reconstructs a footprint nor rescans earlier payloads. The layout
capacity bounds its scalar/control copies at the local address width. -/
namespace Blotto.GeneralPaperLastRegionSelection
open GeneralPaperSequentialLayout GeneralPaperMeasuredBlockPlan
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def price (S A : ℕ) (region : Region A) : ℕ :=
  GeneralPaperEncodedScalarStorage.natBits region.start + GeneralPaperEncodedScalarStorage.natBits region.length +
    2 * A + 64 * (S + A + 1)

def run (S A : ℕ) : List (Region A) → Option (Region A) × ℕ
  | [] => (none,64 * (S + A + 1))
  | region :: regions =>
    let later := run S A regions
    (some (later.1.getD region),later.2 + price S A region)

theorem data (S A : ℕ) (regions : List (Region A)) : (run S A regions).1 = regions.getLast? := by
  induction regions with
  | nil => rfl
  | cons region regions ih => simp only [run,ih,List.getLast?_cons]

theorem nonempty (S A : ℕ) (regions : List (Region A)) (hNonempty : regions ≠ []) :
    ∃ region,(run S A regions).1 = some region := by
  cases regions with
  | nil => exact False.elim (hNonempty rfl)
  | cons region regions => exact ⟨(run S A regions).1.getD region,rfl⟩

theorem member (S A : ℕ) (regions : List (Region A)) (region : Region A) (hResult : (run S A regions).1 = some region) :
    region ∈ regions := by
  rw [data] at hResult
  exact List.mem_of_getLast? hResult

theorem work (S A : ℕ) (regions : List (Region A)) :
    (run S A regions).2 = (regions.map (price S A)).sum + 64 * (S + A + 1) := by
  induction regions with
  | nil => simp only [run,List.map_nil,List.sum_nil,Nat.zero_add]
  | cons region regions ih => simp only [run,ih,List.map_cons,List.sum_cons]; omega

theorem layout_price (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ region ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1,
      price S A region ≤ 4 * A + 2 + 64 * (S + A + 1) := by
  intro region hr
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan region hr
  have hStart := GeneralPaperMeasuredBlockLayout.reference_width model S A start plan hA hCap region hr
  have hLength := binaryWordWidth_le_of_lt_pow hA
    (by unfold Region.stop at hRange; omega : region.length < 2 ^ A)
  unfold price GeneralPaperEncodedScalarStorage.natBits
  omega

theorem bounded_work (S A : ℕ) (regions : List (Region A)) (P : ℕ) (hPrice : ∀ region ∈ regions,price S A region ≤ P) :
    (run S A regions).2 ≤ regions.length * P + 64 * (S + A + 1) := by
  induction regions with
  | nil => simp only [run,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons region regions ih =>
    have hp := hPrice region (List.mem_cons_self ..)
    have ht := ih (fun region hr => hPrice region (List.mem_cons_of_mem _ hr))
    dsimp only [run,List.length_cons]
    nlinarith only [hp,ht]

theorem layout_work (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hA : 1 ≤ A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (run S A (GeneralPaperMeasuredBlockLayout.run model S A start plan).1).2 ≤
      plan.sizes.length * (4 * A + 2 + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  have h := bounded_work S A (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 _
    (layout_price model S A start plan hA hCap)
  rw [GeneralPaperMeasuredBlockLayout.count] at h
  exact h

end Blotto.GeneralPaperLastRegionSelection
