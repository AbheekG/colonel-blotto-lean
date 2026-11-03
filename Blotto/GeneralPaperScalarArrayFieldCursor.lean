import Blotto.GeneralPaperScalarFieldCursor

/-! A scalar-array header is constructed from its actual consumed payload
roots. The parser advances once through the source and regions, leaving the
next field's suffix intact. Header targets are copied by a priced traversal. -/
namespace Blotto.GeneralPaperScalarArrayFieldCursor
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue GeneralPaperReferenceRegionSlots
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def targets (S A : ℕ) : List (Cell A) → List (FixedBinaryWord A) × ℕ
  | [] => ([],64 * (S + A + 1))
  | cell :: cells =>
    let later := targets S A cells
    (cell.region.reference :: later.1,later.2 + A + 64 * (S + A + 1))

theorem targets_data (S A : ℕ) (cells : List (Cell A)) :
    (targets S A cells).1 = cells.map (fun cell => cell.region.reference) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simp only [targets,ih,List.map_cons]

theorem targets_work (S A : ℕ) (cells : List (Cell A)) :
    (targets S A cells).2 = cells.length * (A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction cells with
  | nil => simp only [targets,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons cell cells ih => simp only [targets,ih,List.length_cons]; ring

structure Fields (A : ℕ) where
  header : Header A
  cells : List (Cell A)

def fields (A : ℕ) (header : Region A) (cells : List (Cell A)) : Fields A :=
  ⟨⟨header,64,cells.map (fun cell => cell.region.reference)⟩,cells⟩

structure Result (A : ℕ) where
  values : Option (Fields A)
  remaining : List (Region A)
  work : ℕ

def run (S A : ℕ) (values : List Scalar) : List (Region A) → Result A
  | [] => ⟨none,[],64 * (S + A + 1)⟩
  | header :: regions =>
    let payloads := GeneralPaperScalarFieldCursor.run S A values regions
    match payloads.values with
    | none => ⟨none,payloads.remaining,payloads.work + GeneralPaperLastRegionSelection.price S A header + 64 * (S + A + 1)⟩
    | some cells =>
      let references := targets S A cells
      ⟨some ⟨⟨header,64,references.1⟩,cells⟩,payloads.remaining,
        payloads.work + references.2 + GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1)⟩

theorem on_prefix (S A : ℕ) (header : Region A) (regions rest : List (Region A)) (values : List Scalar)
    (hLength : regions.length = values.length) :
    (run S A values (header :: (regions ++ rest))).values =
        some (fields A header (GeneralPaperScalarFieldCursor.cells A regions values)) ∧
      (run S A values (header :: (regions ++ rest))).remaining = rest := by
  obtain ⟨hv,hr⟩ := GeneralPaperScalarFieldCursor.on_prefix S A regions rest values hLength
  simp only [run,hv,hr,targets_data,fields,and_self]

theorem header_valid (A : ℕ) (header : Region A) (regions : List (Region A)) (values : List Scalar)
    (hLength : regions.length = values.length) (hHeader : header.length = A * (64 + values.length)) :
    Valid (fields A header (GeneralPaperScalarFieldCursor.cells A regions values)).header := by
  have h := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at h
  change A * (64 + ((GeneralPaperScalarFieldCursor.cells A regions values).map (fun cell => cell.region.reference)).length) ≤ header.length
  simp only [List.length_map]
  rw [h,hHeader]

def layoutHeader (A start count : ℕ) : Region A := ⟨start,A * (64 + count),FixedBinaryWord.ofNat A start⟩

theorem layout_regions (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) :
    (GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: values.map encode)).1 =
      layoutHeader A start values.length ::
        (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1 := by
  simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,layoutHeader]

theorem layout_success (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (rest : List (Region A)) :
    let payloads := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1
    let actual := fields A (layoutHeader A start values.length) (GeneralPaperScalarFieldCursor.cells A payloads values)
    (run S A values ((GeneralPaperSequentialLayout.run model S A start
      (A * (64 + values.length) :: values.map encode)).1 ++ rest)).values = some actual ∧
      (run S A values ((GeneralPaperSequentialLayout.run model S A start
        (A * (64 + values.length) :: values.map encode)).1 ++ rest)).remaining = rest ∧
      Valid actual.header ∧ ∀ cell ∈ actual.cells,cell.Fits := by
  dsimp only
  have hLength : (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1.length =
      values.length := by rw [GeneralPaperSequentialLayout.count,List.length_map]
  rw [layout_regions,List.cons_append]
  obtain ⟨hv,hr⟩ := on_prefix S A _ _ rest values hLength
  refine ⟨hv,hr,header_valid A _ _ values hLength rfl,?_⟩
  exact GeneralPaperScalarFieldCursor.cells_fit A _ values (GeneralPaperSequentialLayout.lengths model S A _ _)

end Blotto.GeneralPaperScalarArrayFieldCursor
