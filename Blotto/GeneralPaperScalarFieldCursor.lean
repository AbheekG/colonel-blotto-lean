import Blotto.GeneralPaperRegionCursor

/-! A source-scalar traversal consumes its actual allocated regions once.
The generated payload entries preserve source order and measured scalar sizes;
continuation starts at the untouched region suffix. Scalar copies are priced
by complete encoded length, including the single original-budget cell. -/
namespace Blotto.GeneralPaperScalarFieldCursor
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Cell (A : ℕ) where
  region : Region A
  value : Scalar

def Cell.entry {A : ℕ} (cell : Cell A) : GeneralPaperPayloadMemory.Entry A Scalar := (cell.region.reference,cell.value)
def Cell.Fits {A : ℕ} (cell : Cell A) : Prop := cell.region.length = encode cell.value

def cells (A : ℕ) (regions : List (Region A)) (values : List Scalar) : List (Cell A) :=
  (regions.zip values).map (fun pair => ⟨pair.1,pair.2⟩)

structure Result (A : ℕ) where
  values : Option (List (Cell A))
  remaining : List (Region A)
  work : ℕ

def run (S A : ℕ) : List Scalar → List (Region A) → Result A
  | [],regions => ⟨some [],regions,64 * (S + A + 1)⟩
  | _ :: _,[] => ⟨none,[],64 * (S + A + 1)⟩
  | value :: values,region :: regions =>
    let later := run S A values regions
    ⟨later.values.map (List.cons ⟨region,value⟩),later.remaining,
      later.work + GeneralPaperLastRegionSelection.price S A region + encode value + 64 * (S + A + 1)⟩

theorem cells_regions (A : ℕ) (regions : List (Region A)) (values : List Scalar) (hLength : regions.length = values.length) :
    (cells A regions values).map Cell.region = regions := by
  have h := List.map_fst_zip (show regions.length ≤ values.length by omega)
  simpa only [cells,List.map_map,Function.comp_def] using h

theorem cells_values (A : ℕ) (regions : List (Region A)) (values : List Scalar) (hLength : regions.length = values.length) :
    (cells A regions values).map Cell.value = values := by
  have h := List.map_snd_zip (show values.length ≤ regions.length by omega)
  simpa only [cells,List.map_map,Function.comp_def] using h

theorem cells_keys (A : ℕ) (regions : List (Region A)) (values : List Scalar) (hLength : regions.length = values.length) :
    ((cells A regions values).map (fun cell => cell.entry.1.value)) = regions.map (fun region => region.reference.value) := by
  have h := congrArg (List.map (fun region : Region A => region.reference.value)) (cells_regions A regions values hLength)
  simpa only [List.map_map,Cell.entry,Function.comp_def] using h

theorem cells_fit (A : ℕ) (regions : List (Region A)) (values : List Scalar)
    (hWidths : regions.map Region.length = values.map encode) :
    ∀ cell ∈ cells A regions values,cell.Fits := by
  induction regions generalizing values with
  | nil => simp only [cells,List.zip_nil_left,List.map_nil,List.not_mem_nil,false_implies,implies_true]
  | cons region regions ih =>
    cases values with
    | nil => simp only [List.map_cons,List.map_nil] at hWidths; cases hWidths
    | cons value values =>
      have hPair := List.cons.inj hWidths
      intro cell hc
      simp only [cells,List.zip_cons_cons,List.map_cons,List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hPair.1
      · exact ih values hPair.2 cell hc

theorem on_prefix (S A : ℕ) (regions rest : List (Region A)) (values : List Scalar)
    (hLength : regions.length = values.length) :
    (run S A values (regions ++ rest)).values = some (cells A regions values) ∧
      (run S A values (regions ++ rest)).remaining = rest := by
  induction values generalizing regions with
  | nil =>
    have hNil : regions = [] := List.length_eq_zero_iff.mp hLength
    subst regions
    exact ⟨rfl,rfl⟩
  | cons value values ih =>
    cases regions with
    | nil => simp only [List.length_nil,List.length_cons] at hLength; omega
    | cons region regions =>
      have hTail : regions.length = values.length := by simp only [List.length_cons] at hLength; omega
      obtain ⟨hv,hr⟩ := ih regions hTail
      simp only [List.cons_append,run,hv,hr,cells,List.zip_cons_cons,List.map_cons,Option.map_some,and_self]

theorem layout_success (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1
    (run S A values (regions ++ rest)).values = some (cells A regions values) ∧
      (run S A values (regions ++ rest)).remaining = rest ∧
      ∀ cell ∈ cells A regions values,cell.Fits := by
  dsimp only
  have hLength : (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1.length = values.length := by
    rw [GeneralPaperSequentialLayout.count,List.length_map]
  obtain ⟨hv,hr⟩ := on_prefix S A _ rest values hLength
  exact ⟨hv,hr,cells_fit A _ values (GeneralPaperSequentialLayout.lengths model S A start (values.map encode))⟩

theorem work_on_prefix (S A : ℕ) (regions rest : List (Region A)) (values : List Scalar)
    (hLength : regions.length = values.length) :
    (run S A values (regions ++ rest)).work = (regions.map (GeneralPaperLastRegionSelection.price S A)).sum +
      (values.map encode).sum + values.length * (64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction values generalizing regions with
  | nil =>
    have hNil : regions = [] := List.length_eq_zero_iff.mp hLength
    subst regions
    simp only [List.nil_append,run,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons value values ih =>
    cases regions with
    | nil => simp only [List.length_nil,List.length_cons] at hLength; omega
    | cons region regions =>
      have hTail : regions.length = values.length := by simp only [List.length_cons] at hLength; omega
      change (run S A values (regions ++ rest)).work + GeneralPaperLastRegionSelection.price S A region + encode value +
        64 * (S + A + 1) = _
      rw [ih regions hTail]
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      ring

end Blotto.GeneralPaperScalarFieldCursor
