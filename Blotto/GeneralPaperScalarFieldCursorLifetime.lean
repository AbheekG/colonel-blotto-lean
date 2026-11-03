import Blotto.GeneralPaperSelectedMeasurementInputLifetime

/-! Full scalar extraction from an actual region prefix. Saved scalars,
descriptor/read/copy scratch and recursive control/partial prices coexist
with one output cell list. Scalar precision is an additive sum. The
following region suffix is shared and is never scanned by the observer. -/
namespace Blotto.GeneralPaperScalarFieldCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperScalarFieldCursor (Cell run cells)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds price_word)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def controls (S A : ℕ) (value : Scalar) (values : List Scalar) (region : Region A) (regions : List (Region A)) : List ℕ :=
  [S,A,(run S A values regions).work,GeneralPaperLastRegionSelection.price S A region,
    (run S A values regions).work + GeneralPaperLastRegionSelection.price S A region,
    (run S A values regions).work + GeneralPaperLastRegionSelection.price S A region + encode value,
    (run S A (value :: values) (region :: regions)).work]

def frames (S A : ℕ) : List Scalar → List (Region A) → ℕ
  | [],regions => fields S [S,A,(run S A [] regions).work] + 64 * S
  | _ :: _,[] => fields S [S,A,(run S A [] []).work] + 64 * S
  | value :: values,region :: regions =>
    GeneralPaperFieldDirectoryStorage.cellFoot S (⟨region,value⟩ : Cell A) + encode value +
      GeneralPaperLastRegionSelection.price S A region + fields S (controls S A value values region regions) + 128 * S +
      frames S A values regions

theorem frames_bound (model : RationalCostModel) (S A Q : ℕ) (first rest : List (Region A)) (values : List Scalar)
    (hA : 0 < A) (hLength : first.length = values.length) (hCap : ∀ region ∈ first,region.stop < 2 ^ A)
    (hWork : (run S A values (first ++ rest)).work ≤ Q) :
    frames S A values (first ++ rest) ≤ 2 * (values.map encode).sum + (values.length + 1) * unit model S A Q := by
  induction values generalizing first with
  | nil =>
    have he : first = [] := List.length_eq_zero_iff.mp hLength
    subst first
    simp only [List.nil_append] at hWork
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(run S A [] rest).work] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [List.nil_append,frames,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
    omega
  | cons value values ih =>
    cases first with
    | nil => simp only [List.length_nil,List.length_cons] at hLength; omega
    | cons region regions =>
      have hWhole := hWork
      simp only [List.cons_append] at hWhole
      change (run S A values (regions ++ rest)).work + GeneralPaperLastRegionSelection.price S A region +
        encode value + 64 * (S + A + 1) ≤ Q at hWork
      have hh : region ∈ region :: regions := List.mem_cons_self ..
      have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A region hA (hCap region hh)
      have hRead := GeneralPaperDirectoryCopyWork.region_work model S A region hA (hCap region hh)
      have ht := ih regions (by simp only [List.length_cons] at hLength; omega)
        (fun r hr => hCap r (List.mem_cons_of_mem _ hr)) (by omega)
      have hFields := fields_bound S (natBits (cap S A Q)) (controls S A value values region (regions ++ rest)) (by
        intro x hx
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
        unfold cap
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
      change fields S _ ≤ 7 * (natBits (cap S A Q) + S) + 32 * S at hFields
      have hUnit := unit_bounds model S A Q
      have hRegionFoot := hRegion
      unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegionFoot
      have hLocal : GeneralPaperFieldDirectoryStorage.cellFoot S (⟨region,value⟩ : Cell A) + encode value +
          GeneralPaperLastRegionSelection.price S A region + fields S (controls S A value values region (regions ++ rest)) + 128 * S ≤
          2 * encode value + unit model S A Q := by
        dsimp only [GeneralPaperFieldDirectoryStorage.cellFoot]
        omega
      simp only [List.cons_append,frames,List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hLocal,ht]

theorem output_cells_bound (S A : ℕ) (first : List (Region A)) (values : List Scalar) (hA : 0 < A)
    (hLength : first.length = values.length) (hCap : ∀ region ∈ first,region.stop < 2 ^ A) :
    listFootprint S (GeneralPaperFieldDirectoryStorage.cellFoot S) (cells A first values) ≤
      (values.map encode).sum + values.length * (192 * (S + A + 1) + 2 * S) + 32 * S := by
  have hRegions := GeneralPaperScalarFieldCursor.cells_regions A first values hLength
  have hValues := GeneralPaperScalarFieldCursor.cells_values A first values hLength
  have hCells := GeneralPaperFieldDirectoryStorage.cells_bound S A (cells A first values) (by
    intro cell hc
    have hm : cell.region ∈ first := by rw [← hRegions]; exact List.mem_map.mpr ⟨cell,hc,rfl⟩
    exact GeneralPaperMeasuredLayoutStorage.region_bound S A cell.region hA (hCap cell.region hm))
  have hCount := congrArg List.length hValues
  simp only [List.length_map] at hCount
  have hPayload := congrArg (fun xs => (xs.map encode).sum) hValues
  simp only [List.map_map,Function.comp_def] at hPayload
  rw [hPayload,hCount] at hCells
  change (List.map (GeneralPaperFieldDirectoryStorage.cellFoot S) (cells A first values)).sum +
    (cells A first values).length * (2 * S) + 32 * S ≤ _
  rw [hCount]
  nlinarith only [hCells]

def window (S A : ℕ) (values : List Scalar) (first rest : List (Region A)) : ℕ :=
  listFootprint S encode values + GeneralPaperMeasuredLayoutStorage.regionsFoot S first +
    listFootprint S (GeneralPaperFieldDirectoryStorage.cellFoot S) (cells A first values) + frames S A values (first ++ rest) +
    fields S [S,A,(run S A values (first ++ rest)).work] + 64 * S

theorem window_bound (model : RationalCostModel) (S A Q : ℕ) (first rest : List (Region A)) (values : List Scalar)
    (hA : 0 < A) (hLength : first.length = values.length) (hCap : ∀ region ∈ first,region.stop < 2 ^ A)
    (hWork : (run S A values (first ++ rest)).work ≤ Q) :
    window S A values first rest ≤ ((values.map encode).sum + 1) * 8 * unit model S A Q := by
  have hFrames := frames_bound model S A Q first rest values hA hLength hCap hWork
  have hCells := output_cells_bound S A first values hA hLength hCap
  have hRegions := list_bound S (GeneralPaperMeasuredLayoutStorage.regionBound S A)
    (GeneralPaperMeasuredLayoutStorage.regionFoot S) first (fun r hr => GeneralPaperMeasuredLayoutStorage.region_bound S A r hA (hCap r hr))
  rw [hLength] at hRegions
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(run S A values (first ++ rest)).work] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hCount := GeneralPaperScalarCursorWork.count_le_payload values
  have hUnit := unit_bounds model S A Q
  have hMetadata : GeneralPaperMeasuredLayoutStorage.regionBound S A + 192 * (S + A + 1) + 6 * S ≤ unit model S A Q := by
    unfold GeneralPaperMeasuredLayoutStorage.regionBound
    omega
  have hLinks := Nat.mul_le_mul_left values.length hMetadata
  have hN := Nat.mul_le_mul_right (unit model S A Q) hCount
  have hOne : 3 ≤ unit model S A Q := by omega
  have hPayload := Nat.mul_le_mul_left (values.map encode).sum hOne
  unfold window GeneralPaperMeasuredLayoutStorage.regionsFoot
  change (values.map encode).sum + values.length * (2 * S) + 32 * S + _ + _ + _ + _ + 64 * S ≤ _
  nlinarith only [hFrames,hCells,hRegions,hFields,hLinks,hN,hPayload,hUnit]

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (B + 1) * 8 * unit model S A ((B + 1) * 4 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem layout_bound (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + (values.map encode).sum < 2 ^ A) :
    window S A values (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1 rest ≤
      profile model S A (values.map encode).sum := by
  have hRange := GeneralPaperSequentialLayout.range model S A start (values.map encode)
  exact window_bound model S A _ _ rest values hA
    (by rw [GeneralPaperSequentialLayout.count,List.length_map])
    (fun region hr => (hRange region hr).2.trans_lt hCap)
    (GeneralPaperScalarCursorWork.layout model S A start values rest hA hCap)

theorem unchanged_suffix (S A : ℕ) (first rest : List (Region A)) (values : List Scalar)
    (hLength : first.length = values.length) : (run S A values (first ++ rest)).remaining = rest :=
  (GeneralPaperScalarFieldCursor.on_prefix S A first rest values hLength).2

end Blotto.GeneralPaperScalarFieldCursorLifetime
