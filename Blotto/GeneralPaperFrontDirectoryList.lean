import Blotto.GeneralPaperPreparedRecordInstallation

/-! A front list header indexes actual child roots inside its existing
32-word-prefix/two-word-per-item region. The checked indexed-storage backend
uses a packed target table within that region. Field schemas are proof-only. -/
namespace Blotto.GeneralPaperFrontDirectoryList
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperReferenceRegionSlots (Header)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def compose {A : ℕ} (header : Region A) (body : Body A) : Directory A :=
  ⟨header,⟨header,32,body.roots.map Region.reference⟩ :: body.headers,body.cells⟩

def run {α : Type*} (S A : ℕ) (parser : Parser α A) (values : List α) : List (Region A) → GeneralPaperFieldDirectoryParsers.Result A
  | [] => ⟨none,[],64 * (S + A + 1)⟩
  | header :: regions =>
    let children := GeneralPaperChildDirectoryCursor.run S A parser values regions
    match children.values with
    | none => ⟨none,children.remaining,children.work + 64 * (S + A + 1)⟩
    | some body =>
      let targets := GeneralPaperNestedArrayFieldCursor.rootWords S A body.roots
      ⟨some ⟨header,⟨header,32,targets.1⟩ :: body.headers,body.cells⟩,children.remaining,
        children.work + targets.2 + GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1)⟩

theorem compose_safe (A : ℕ) (header : Region A) (regions : List (Region A)) (body : Body A)
    (hBody : SafeBody regions body) (hSize : A * (32 + body.roots.length) ≤ header.length) :
    Safe (header :: regions) (compose header body) := by
  refine ⟨List.mem_cons_self ..,hBody.2.1.cons_cons header,hBody.2.2.1.cons header,?_,hBody.2.2.2.2⟩
  intro actual ha
  rcases List.mem_cons.mp ha with rfl | ha
  · change A * (32 + (body.roots.map Region.reference).length) ≤ header.length
    simpa only [List.length_map] using hSize
  · exact hBody.2.2.2.1 actual ha

def expected {α : Type*} (A start : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α) : Directory A :=
  compose (GeneralPaperScalarRecordComponents.listHeader A start 32 2 values.length)
    (GeneralPaperChildDirectorySpecification.collect (GeneralPaperChildDirectorySpecification.directories schema child
      (start + A * (2 * values.length + 32)) values))

theorem success {α : Type*} (model : RationalCostModel) (S A : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (child : α → ℕ → Directory A)
    (hParser : ∀ value start rest,
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).values = some (child value start) ∧
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).remaining = rest ∧
      Safe (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (child value start))
    (hCovered : ∀ value start,Covered (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (child value start))
    (start : ℕ) (values : List α) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (A * (2 * values.length + 32) :: (values.map schema).flatten)).1
    (run S A parser values (regions ++ rest)).values = some (expected A start schema child values) ∧
      (run S A parser values (regions ++ rest)).remaining = rest ∧
      Safe regions (expected A start schema child values) ∧ Covered regions (expected A start schema child values) := by
  dsimp only
  let header := GeneralPaperScalarRecordComponents.listHeader A start 32 2 values.length
  let next := start + A * (2 * values.length + 32)
  let regions := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1
  let body := GeneralPaperChildDirectorySpecification.collect (GeneralPaperChildDirectorySpecification.directories schema child next values)
  obtain ⟨hv,hr,hs⟩ := GeneralPaperChildDirectorySpecification.success model S A parser schema child hParser next values rest
  change (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).values = some body at hv
  change (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).remaining = rest at hr
  have hCount := GeneralPaperChildDirectoryCursor.root_count S A parser values _ body hv
  have hRegions : (GeneralPaperSequentialLayout.run model S A start (A * (2 * values.length + 32) :: (values.map schema).flatten)).1 = header :: regions := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header,regions,next,GeneralPaperScalarRecordComponents.listHeader]
  rw [hRegions,List.cons_append]
  refine ⟨?_,?_,compose_safe A header regions body hs ?_,?_⟩
  · simp only [run,hv,hr,GeneralPaperNestedArrayFieldCursor.root_words_data,expected,compose]
    rfl
  · simp only [run,hv,hr]
  · change A * (32 + body.roots.length) ≤ A * (2 * values.length + 32)
    rw [hCount]
    apply Nat.mul_le_mul_left
    omega
  · exact (GeneralPaperFieldDirectoryPartition.children model S A schema child hCovered next values).cons header

end Blotto.GeneralPaperFrontDirectoryList
