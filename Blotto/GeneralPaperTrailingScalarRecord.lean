import Blotto.GeneralPaperUnifiedMatrixInstallation

/-! Forward extraction for scalar fields followed by their reserved record.
The root and all targets come from consumed actual regions. No field size,
directory or decoded target is supplied to the executed cursor. -/
namespace Blotto.GeneralPaperTrailingScalarRecord
open GeneralPaperSequentialLayout GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def compose {A : ℕ} (header : Region A) (cells : List (Cell A)) : Directory A :=
  ⟨header,[⟨header,0,cells.map (fun cell => cell.region.reference)⟩],cells⟩

def run (S A : ℕ) (values : List Scalar) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  let parsed := GeneralPaperScalarFieldCursor.run S A values regions
  match parsed.values,parsed.remaining with
  | some cells,header :: rest =>
    let references := GeneralPaperScalarArrayFieldCursor.targets S A cells
    ⟨some ⟨header,[⟨header,0,references.1⟩],cells⟩,rest,
      parsed.work + references.2 + GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1)⟩
  | _,_ => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩

def header (A start arity : ℕ) : Region A := ⟨start,A * arity,FixedBinaryWord.ofNat A start⟩

def expected (model : RationalCostModel) (S A start arity : ℕ) (values : List Scalar) : Directory A :=
  compose (header A (start + (values.map encode).sum) arity)
    (GeneralPaperScalarFieldCursor.cells A (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1 values)

theorem on_prefix (S A : ℕ) (regions : List (Region A)) (record : Region A) (rest : List (Region A))
    (values : List Scalar) (hLength : regions.length = values.length) :
    (run S A values (regions ++ record :: rest)).values =
        some (compose record (GeneralPaperScalarFieldCursor.cells A regions values)) ∧
      (run S A values (regions ++ record :: rest)).remaining = rest := by
  obtain ⟨hv,hr⟩ := GeneralPaperScalarFieldCursor.on_prefix S A regions (record :: rest) values hLength
  simp only [run,hv,hr,GeneralPaperScalarArrayFieldCursor.targets_data,compose,and_self]

theorem layout_regions (model : RationalCostModel) (S A start arity : ℕ) (values : List Scalar) :
    (GeneralPaperSequentialLayout.run model S A start (values.map encode ++ [A * arity])).1 =
      (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1 ++
        [header A (start + (values.map encode).sum) arity] := by
  rw [GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
  simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header]

theorem compose_safe (A : ℕ) (regions : List (Region A)) (record : Region A) (values : List Scalar)
    (hLength : regions.length = values.length) (hWidths : regions.map Region.length = values.map encode)
    (hHeader : A * values.length ≤ record.length) :
    Safe (regions ++ [record]) (compose record (GeneralPaperScalarFieldCursor.cells A regions values)) := by
  have hRegions := GeneralPaperScalarFieldCursor.cells_regions A regions values hLength
  have hCount := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at hCount
  refine ⟨List.mem_append_right _ (List.mem_singleton_self _),?_,?_,?_,?_⟩
  · change [record].Sublist (regions ++ [record])
    simpa only [List.nil_append] using (List.nil_sublist regions).append (List.Sublist.refl [record])
  · change ((GeneralPaperScalarFieldCursor.cells A regions values).map Cell.region).Sublist (regions ++ [record])
    rw [hRegions]
    simpa only [List.append_nil] using (List.Sublist.refl regions).append (List.nil_sublist [record])
  · intro actual ha
    have he' : actual = (⟨record,0,(GeneralPaperScalarFieldCursor.cells A regions values).map (fun cell => cell.region.reference)⟩ :
        GeneralPaperReferenceRegionSlots.Header A) := List.mem_singleton.mp ha
    subst actual
    change A * (0 + ((GeneralPaperScalarFieldCursor.cells A regions values).map (fun cell => cell.region.reference)).length) ≤ record.length
    simpa only [List.length_map,Nat.zero_add,hCount] using hHeader
  · exact GeneralPaperScalarFieldCursor.cells_fit A regions values hWidths

theorem compose_covered (A : ℕ) (regions : List (Region A)) (record : Region A) (values : List Scalar)
    (hLength : regions.length = values.length) :
    Covered (regions ++ [record]) (compose record (GeneralPaperScalarFieldCursor.cells A regions values)) := by
  change ([record] ++ (GeneralPaperScalarFieldCursor.cells A regions values).map Cell.region).Perm (regions ++ [record])
  rw [GeneralPaperScalarFieldCursor.cells_regions A regions values hLength]
  exact List.perm_append_comm

theorem success (model : RationalCostModel) (S A start arity : ℕ) (values : List Scalar)
    (rest : List (Region A)) (hArity : values.length ≤ arity) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (values.map encode ++ [A * arity])).1
    (run S A values (regions ++ rest)).values = some (expected model S A start arity values) ∧
      (run S A values (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A start arity values) ∧ Covered regions (expected model S A start arity values) := by
  dsimp only
  have hLength : (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1.length = values.length := by
    rw [GeneralPaperSequentialLayout.count,List.length_map]
  rw [layout_regions,List.append_assoc,List.singleton_append]
  obtain ⟨hv,hr⟩ := on_prefix S A _ _ rest values hLength
  refine ⟨hv,hr,compose_safe A _ _ values hLength
    (GeneralPaperSequentialLayout.lengths model S A start (values.map encode)) (Nat.mul_le_mul_left A hArity),
    compose_covered A _ _ values hLength⟩

theorem work_on_prefix (S A : ℕ) (regions : List (Region A)) (record : Region A) (rest : List (Region A))
    (values : List Scalar) (hLength : regions.length = values.length) :
    (run S A values (regions ++ record :: rest)).work =
      (GeneralPaperScalarFieldCursor.run S A values (regions ++ record :: rest)).work +
      values.length * (A + 64 * (S + A + 1)) + GeneralPaperLastRegionSelection.price S A record + 192 * (S + A + 1) := by
  obtain ⟨hv,hr⟩ := GeneralPaperScalarFieldCursor.on_prefix S A regions (record :: rest) values hLength
  have hCount := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at hCount
  simp only [run,hv,hr,GeneralPaperScalarArrayFieldCursor.targets_work,hCount]
  ring

end Blotto.GeneralPaperTrailingScalarRecord
