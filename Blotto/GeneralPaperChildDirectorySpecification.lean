import Blotto.GeneralPaperChildDirectoryCursor

/-! Component-correct child parsers compose on the actual flattened layout.
Expected directories and schemas below are erased specification observers;
the executed child loop receives only its concrete parser, source and stream.
The concrete matrix instance discharges the component premise from its fixed
checked rational-array parser. -/
namespace Blotto.GeneralPaperChildDirectorySpecification
open GeneralPaperFieldDirectory GeneralPaperFieldDirectoryParsers GeneralPaperSequentialLayout
open GeneralPaperFieldDirectorySafety
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def directories {α : Type*} {A : ℕ} (schema : α → List ℕ) (expected : α → ℕ → Directory A) : ℕ → List α → List (Directory A)
  | _,[] => []
  | start,value :: values => expected value start :: directories schema expected (start + (schema value).sum) values

def collect {A : ℕ} (directories : List (Directory A)) : Body A :=
  ⟨directories.map Directory.root,(directories.map Directory.headers).flatten,(directories.map Directory.cells).flatten⟩

theorem collect_cons (S A : ℕ) (directory : Directory A) (tail : List (Directory A)) :
    collect (directory :: tail) = (GeneralPaperFieldDirectory.prepend S A directory (collect tail)).1 := by
  simp only [collect,List.map_cons,List.flatten_cons,GeneralPaperFieldDirectory.prepend,
    append_headers_data,append_cells_data]

theorem directory_count {α : Type*} {A : ℕ} (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (start : ℕ) (values : List α) : (directories schema expected start values).length = values.length := by
  induction values generalizing start with
  | nil => rfl
  | cons value values ih => simp only [directories,List.length_cons,ih]

theorem success {α : Type*} (model : RationalCostModel) (S A : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (hParser : ∀ value start rest,
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).values =
          some (expected value start) ∧
        (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).remaining = rest ∧
        Safe (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (expected value start))
    (start : ℕ) (values : List α) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1
    let actual := collect (directories schema expected start values)
    (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).values = some actual ∧
      (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).remaining = rest ∧ SafeBody regions actual := by
  induction values generalizing start with
  | nil =>
    dsimp only [List.map_nil,List.flatten_nil,GeneralPaperSequentialLayout.run,List.nil_append,
      GeneralPaperChildDirectoryCursor.run,directories,collect]
    refine ⟨rfl,rfl,?_⟩
    simp only [SafeBody,List.flatten_nil,GeneralPaperSequentialLayout.run,List.not_mem_nil,false_implies,implies_true,List.map_nil,List.nil_sublist,and_self]
  | cons value values ih =>
    dsimp only
    let first := (GeneralPaperSequentialLayout.run model S A start (schema value)).1
    let next := start + (schema value).sum
    let later := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1
    let head := expected value start
    let tail := collect (directories schema expected next values)
    have hRegions : (GeneralPaperSequentialLayout.run model S A start ((value :: values).map schema).flatten).1 = first ++ later := by
      rw [List.map_cons,List.flatten_cons,GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
    have hHead := hParser value start (later ++ rest)
    change (parser value (first ++ (later ++ rest))).values = some head ∧
      (parser value (first ++ (later ++ rest))).remaining = later ++ rest ∧ Safe first head at hHead
    have hTail := ih next
    change (GeneralPaperChildDirectoryCursor.run S A parser values (later ++ rest)).values = some tail ∧
      (GeneralPaperChildDirectoryCursor.run S A parser values (later ++ rest)).remaining = rest ∧ SafeBody later tail at hTail
    have hTailValues : (GeneralPaperChildDirectoryCursor.run S A parser values
        (parser value (first ++ (later ++ rest))).remaining).values = some tail := by rw [hHead.2.1]; exact hTail.1
    have hStep := GeneralPaperChildDirectoryCursor.step S A parser value values (first ++ (later ++ rest)) head tail hHead.1 hTailValues
    have hRemain : (GeneralPaperChildDirectoryCursor.run S A parser (value :: values) (first ++ (later ++ rest))).remaining = rest := by
      rw [hStep.2.1,hHead.2.1]
      exact hTail.2.1
    have hSafe := GeneralPaperFieldDirectorySafety.prepend S A first later head tail hHead.2.2 hTail.2.2
    have hExpected : collect (directories schema expected start (value :: values)) =
        (GeneralPaperFieldDirectory.prepend S A head tail).1 := by
      change collect (head :: directories schema expected next values) = _
      exact collect_cons S A head _
    simpa only [hRegions,List.append_assoc,hExpected] using And.intro hStep.1 (And.intro hRemain hSafe)

end Blotto.GeneralPaperChildDirectorySpecification
