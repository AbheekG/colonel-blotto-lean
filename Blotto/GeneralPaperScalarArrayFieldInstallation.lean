import Blotto.GeneralPaperMappedScalarArrayCursor

/-! Cursor-extracted scalar arrays install actual raw targets and typed
payload cells. Reads follow root/index -> stored reference -> scalar payload.
Source values and decoded references are not reader inputs. -/
namespace Blotto.GeneralPaperScalarArrayFieldInstallation
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue GeneralPaperReferenceRegionSlots
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperScalarArrayFieldCursor (Fields fields layoutHeader)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Installed (A : ℕ) where
  references : GeneralPaperPayloadMemory.Memory Word
  payloads : GeneralPaperPayloadMemory.Memory Scalar
  root : FixedBinaryWord A
  work : ℕ

def install (model : RationalCostModel) (S A : ℕ) (fields : Fields A) : Installed A :=
  let references := GeneralPaperMixedReferenceRegionProgram.prepare model S A A [] [fields.header]
    (GeneralPaperPayloadMemory.empty Word)
  let payloads := GeneralPaperPayloadMemory.install S A encode (GeneralPaperPayloadMemory.empty Scalar) (fields.cells.map Cell.entry)
  ⟨references.memory,payloads.1,fields.header.region.reference,references.work + payloads.2 + 64 * (S + A + 1)⟩

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : Option Scalar × ℕ :=
  let target := GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 64 index
  match target.1 with
  | none => (none,target.2 + 64 * A + 64)
  | some ⟨B,pointer⟩ =>
    let scalar := GeneralPaperPayloadMemory.read B encode installed.payloads pointer
    (scalar.1,target.2 + scalar.2 + 64 * (A + B + 1))

theorem read_fields (model : RationalCostModel) (S A : ℕ) (header : Region A) (cells : List (Cell A))
    (hA : 0 < A) (hValid : Valid (fields A header cells).header) (hCap : header.stop < 2 ^ A)
    (hRoot : header.reference.value = header.start)
    (hKeys : ((cells.map Cell.entry).map (fun entry => entry.1.value)).Nodup) (j : Fin cells.length) :
    (read model A (install model S A (fields A header cells)) j.val).1 = some (cells[j.val].value) ∧
      (read model A (install model S A (fields A header cells)) j.val).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (install model S A (fields A header cells)).references
          header.reference 64 j.val).2 + encode cells[j.val].value + 192 * A + 128 := by
  let actual := fields A header cells
  have hHeader : actual.header ∈ [actual.header] := List.mem_cons_self ..
  have hAllValid : ∀ h ∈ [actual.header],Valid h := by intro h hh; rcases List.mem_singleton.mp hh with rfl; exact hValid
  have hAllCap : ∀ h ∈ [actual.header],h.region.stop < 2 ^ A := by
    intro h hh; rcases List.mem_singleton.mp hh with rfl; exact hCap
  have hAllRoots : ∀ h ∈ [actual.header],h.region.reference.value = h.region.start := by
    intro h hh; rcases List.mem_singleton.mp hh with rfl; exact hRoot
  have hOwners : GeneralPaperReferenceRegionProgram.DisjointOwners [actual.header] :=
    List.Pairwise.cons (by intro h hh; cases hh) List.Pairwise.nil
  have hTarget := GeneralPaperMixedReferenceRegionProgram.outside_read model S A A [] [actual.header]
    (GeneralPaperPayloadMemory.empty Word) hA hAllValid hAllCap hAllRoots hOwners actual.header hHeader
    ⟨j.val,by change j.val < (cells.map (fun cell => cell.region.reference)).length; rw [List.length_map]; exact j.isLt⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (install model S A actual).references header.reference 64 j.val).1 =
    some (⟨A,(cells.map (fun cell => cell.region.reference))[j.val]'(by rw [List.length_map]; exact j.isLt)⟩ : Word) at hTarget
  simp only [List.getElem_map] at hTarget
  have hEntry : cells[j.val].entry ∈ cells.map Cell.entry :=
    List.mem_map.mpr ⟨cells[j.val],List.getElem_mem j.isLt,rfl⟩
  have hPayload := GeneralPaperPayloadMemory.installed S A encode (GeneralPaperPayloadMemory.empty Scalar)
    (cells.map Cell.entry) hKeys cells[j.val].entry hEntry
  change (install model S A actual).payloads cells[j.val].region.reference.value = some cells[j.val].value at hPayload
  have hInstalledRoot : (install model S A (fields A header cells)).root = header.reference := rfl
  dsimp only [actual] at hTarget hPayload
  dsimp only [read]
  rw [hInstalledRoot]
  simp only [hTarget,GeneralPaperPayloadMemory.read,hPayload,Option.elim_some]
  constructor
  · exact True.intro
  · ring

theorem expected_read (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (hA : 0 < A)
    (hCap : start + (A * (64 + values.length) :: values.map encode).sum < 2 ^ A) (j : Fin values.length) :
    (read model A (install model S A (GeneralPaperMappedScalarArrayCursor.expected model S A start values)) j.val).1 =
      some values[j.val] := by
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1
  let cs := GeneralPaperScalarFieldCursor.cells A regions values
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hCells := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at hCells
  have hPayloadCap : start + A * (64 + values.length) + (values.map encode).sum < 2 ^ A := by
    simp only [List.sum_cons] at hCap
    omega
  have hRegionKeys := GeneralPaperMeasuredLayoutDistinct.reference_values model S A
    (start + A * (64 + values.length)) (⟨values.map encode,0⟩ : GeneralPaperMeasuredBlockPlan.Plan)
    (by intro size hs; obtain ⟨value,_,rfl⟩ := List.mem_map.mp hs; exact positive value) hPayloadCap
  have hKeys : ((cs.map Cell.entry).map (fun entry => entry.1.value)).Nodup := by
    rw [List.map_map]
    change ((GeneralPaperScalarFieldCursor.cells A regions values).map (fun cell => cell.entry.1.value)).Nodup
    rw [GeneralPaperScalarFieldCursor.cells_keys A regions values hLength]
    exact hRegionKeys
  have hHeaderCap : (layoutHeader A start values.length).stop < 2 ^ A := by
    change start + A * (64 + values.length) < 2 ^ A
    omega
  have hRoot : (layoutHeader A start values.length).reference.value = start :=
    FixedBinaryWord.value_ofNat A start (by omega)
  have hRead := read_fields model S A (layoutHeader A start values.length) cs hA
    (GeneralPaperScalarArrayFieldCursor.header_valid A _ regions values hLength rfl) hHeaderCap hRoot hKeys
    ⟨j.val,by change j.val < (GeneralPaperScalarFieldCursor.cells A regions values).length; rw [hCells]; exact j.isLt⟩
  have hValues := congrArg (fun xs : List Scalar => xs[j.val]?) (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  have hIndex : j.val < cs.length := by dsimp only [cs]; rw [hCells]; exact j.isLt
  rw [List.getElem?_map,List.getElem?_eq_getElem hIndex,List.getElem?_eq_getElem j.isLt] at hValues
  have hValue := Option.some.inj hValues
  exact hRead.1.trans (congrArg some hValue)

end Blotto.GeneralPaperScalarArrayFieldInstallation
