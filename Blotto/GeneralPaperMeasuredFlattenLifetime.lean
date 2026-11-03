import Blotto.GeneralPaperMeasuredIndexedArrayLifetime

/-! Full actual size-list flattening. Each left copy is charged locally;
recursive output tails are shared. The original list-of-lists, one complete
flattened output and all saved parent prices coexist in an additive bound. -/
namespace Blotto.GeneralPaperMeasuredFlattenLifetime
open GeneralPaperMeasuredArrayBlockPlan (flatten)
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def controls (S A : ℕ) (xs : List ℕ) (xss : List (List ℕ)) : List ℕ :=
  let later := flatten S xss
  let actual := GeneralPaperMeasuredBlockPlan.append S xs later.1
  [S,A,later.2,actual.2,later.2+actual.2,(flatten S (xs :: xss)).2]

def frames (S A : ℕ) : List (List ℕ) → ℕ
  | [] => fields S [S,A,(flatten S []).2] + 64 * S
  | xs :: xss => appendFrames S A xs (flatten S xss).1 + fields S (controls S A xs xss) + 128 * S + frames S A xss

theorem frames_bound (model : RationalCostModel) (S A Q : ℕ) (xss : List (List ℕ)) (hA : 0 < A)
    (hPos : ∀ xs ∈ xss,∀ x ∈ xs,0 < x) (hCap : (xss.map List.sum).sum < 2 ^ A)
    (hWork : (flatten S xss).2 ≤ Q) :
    frames S A xss ≤ ((xss.map List.sum).sum + xss.length + 1) * 4 * unit model S A Q := by
  induction xss with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(flatten S []).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [frames,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons xs xss ih =>
    have hWhole := hWork
    change (flatten S xss).2 + (GeneralPaperMeasuredBlockPlan.append S xs (flatten S xss).1).2 + 64 * S + 64 ≤ Q at hWork
    have hHeadCap : xs.sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
    have hTailCap : (xss.map List.sum).sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
    have hh : xs ∈ xs :: xss := List.mem_cons_self ..
    have hAppend := append_bound model S A Q xs (flatten S xss).1 hA (hPos xs hh) hHeadCap (by omega)
    have ht := ih (fun ys hy => hPos ys (List.mem_cons_of_mem _ hy)) hTailCap (by omega)
    have hFields := fields_bound S (natBits (cap S A Q)) (controls S A xs xss) (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 6 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    have hParent : fields S (controls S A xs xss) + 128 * S ≤ unit model S A Q := by omega
    simp only [frames,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hAppend,ht,hParent,Nat.zero_le (xs.sum * unit model S A Q)]

theorem size_list_bound (model : RationalCostModel) (S A Q : ℕ) (xs : List ℕ) (hA : 0 < A)
    (hPos : ∀ x ∈ xs,0 < x) (hCap : xs.sum < 2 ^ A) :
    listFootprint S natBits xs ≤ (xs.sum + 1) * unit model S A Q := by
  let plan : GeneralPaperMeasuredBlockPlan.Plan := ⟨xs,0⟩
  have h := plan_bound model S A Q plan hPos hA hCap (by change 0 ≤ Q; omega)
  unfold GeneralPaperMeasuredLayoutStorage.planFoot at h
  change listFootprint S natBits xs + fields S [0] + 64 * S ≤ (xs.sum + 1) * unit model S A Q at h
  omega

theorem source_bound (model : RationalCostModel) (S A Q : ℕ) (xss : List (List ℕ)) (hA : 0 < A)
    (hPos : ∀ xs ∈ xss,∀ x ∈ xs,0 < x) (hCap : (xss.map List.sum).sum < 2 ^ A) :
    listFootprint S (listFootprint S natBits) xss ≤ ((xss.map List.sum).sum + xss.length + 1) * 2 * unit model S A Q := by
  have hSum : (xss.map (listFootprint S natBits)).sum ≤ ((xss.map List.sum).sum + xss.length) * unit model S A Q := by
    induction xss with
    | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.zero_mul,le_refl]
    | cons xs xss ih =>
      have hHeadCap : xs.sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
      have hTailCap : (xss.map List.sum).sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
      have hh : xs ∈ xs :: xss := List.mem_cons_self ..
      have hHead := size_list_bound model S A Q xs hA (hPos xs hh) hHeadCap
      have ht := ih (fun ys hy => hPos ys (List.mem_cons_of_mem _ hy)) hTailCap
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hHead,ht]
  have hUnit := unit_bounds model S A Q
  have hControl : 2 * S + 32 * S ≤ unit model S A Q := by omega
  have hPay := Nat.mul_le_mul_left (xss.length + 1) hControl
  have hMass := Nat.mul_le_mul_right (unit model S A Q)
    (show xss.length + 1 ≤ (xss.map List.sum).sum + xss.length + 1 by omega)
  change (xss.map (listFootprint S natBits)).sum + xss.length * (2 * S) + 32 * S ≤ _
  nlinarith only [hSum,hPay,hMass]

theorem output_bound (model : RationalCostModel) (S A Q : ℕ) (xss : List (List ℕ)) (hA : 0 < A)
    (hPos : ∀ xs ∈ xss,∀ x ∈ xs,0 < x) (hCap : (xss.map List.sum).sum < 2 ^ A) :
    listFootprint S natBits (flatten S xss).1 ≤ ((xss.map List.sum).sum + 1) * unit model S A Q := by
  have hPositive : ∀ x ∈ (flatten S xss).1,0 < x := by
    rw [GeneralPaperMeasuredArrayBlockPlan.flatten_data]
    intro x hx
    obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx
    exact hPos xs hxs x hx
  have h := size_list_bound model S A Q (flatten S xss).1 hA hPositive
    (by rw [GeneralPaperMeasuredArrayBlockPlan.flatten_sum]; exact hCap)
  simpa only [GeneralPaperMeasuredArrayBlockPlan.flatten_sum] using h

def window (S A : ℕ) (xss : List (List ℕ)) : ℕ :=
  listFootprint S (listFootprint S natBits) xss + listFootprint S natBits (flatten S xss).1 + frames S A xss +
    fields S [S,A,(flatten S xss).2] + 64 * S

theorem window_bound (model : RationalCostModel) (S A Q : ℕ) (xss : List (List ℕ)) (hA : 0 < A)
    (hPos : ∀ xs ∈ xss,∀ x ∈ xs,0 < x) (hCap : (xss.map List.sum).sum < 2 ^ A)
    (hWork : (flatten S xss).2 ≤ Q) :
    window S A xss ≤ ((xss.map List.sum).sum + xss.length + 1) * 8 * unit model S A Q := by
  have hFrames := frames_bound model S A Q xss hA hPos hCap hWork
  have hSource := source_bound model S A Q xss hA hPos hCap
  have hOutput := output_bound model S A Q xss hA hPos hCap
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(flatten S xss).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S [S,A,(flatten S xss).2] + 64 * S ≤ unit model S A Q := by omega
  have hOutputFactor := Nat.mul_le_mul_right (unit model S A Q)
    (show (xss.map List.sum).sum + 1 ≤ (xss.map List.sum).sum + xss.length + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ (xss.map List.sum).sum + xss.length + 1 by omega)
  unfold window
  nlinarith only [hFrames,hSource,hOutput,hParent,hOutputFactor,hBase]

end Blotto.GeneralPaperMeasuredFlattenLifetime
