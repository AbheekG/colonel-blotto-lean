import Blotto.GeneralPaperRouteFieldRead

/-! The retained route array fixes each child parser to the concrete route
cursor. Its old measured array plan and complete owner partition are reused;
the outer header contains actual returned route-record roots in source order. -/
namespace Blotto.GeneralPaperRouteArrayCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def schema {m : ℕ} (model : RationalCostModel) (S A : ℕ) (route : GroupRoute m) : List ℕ :=
  (GeneralPaperEqualMeasuredLeafPlans.route model S A route).sizes

def expected {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m)) : Directory A :=
  GeneralPaperNestedArrayFieldCursor.compose (GeneralPaperScalarArrayFieldCursor.layoutHeader A start source.data.toList.length)
    (GeneralPaperChildDirectorySpecification.collect
      (GeneralPaperChildDirectorySpecification.directories (schema model S A) (GeneralPaperRouteFieldCursor.expected model S A)
        (start + A * (64 + source.data.toList.length)) source.data.toList))

def run {n m : ℕ} (S A : ℕ) (source : FixedArrayTable n (GroupRoute m)) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperNestedArrayFieldCursor.runList S A (GeneralPaperRouteFieldCursor.run S A) source.data.toList regions

theorem plan {n m : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n (GroupRoute m)) :
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes =
      A * (64 + source.data.toList.length) :: (source.data.toList.map (schema model S A)).flatten := by
  have hMap := congrArg (List.map (schema model S A)) (GeneralPaperRowPrefix.list_ofFn source)
  simp only [List.map_ofFn,Function.comp_def] at hMap
  rw [GeneralPaperMeasuredArrayBlockPlan.array_data]
  change A * (n + 64) :: (List.ofFn (fun i : Fin n => schema model S A (source.read i))).flatten = _
  rw [hMap,Array.length_toList,source.size]
  congr 1
  ring

theorem success {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m)) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source)).1
    (run S A source (regions ++ rest)).values = some (expected model S A start source) ∧
      (run S A source (regions ++ rest)).remaining = rest ∧ Safe regions (expected model S A start source) := by
  have hParser : ∀ route : GroupRoute m,∀ start rest,
      (GeneralPaperRouteFieldCursor.run S A route ((GeneralPaperSequentialLayout.run model S A start (schema model S A route)).1 ++ rest)).values =
        some (GeneralPaperRouteFieldCursor.expected model S A route start) ∧
      (GeneralPaperRouteFieldCursor.run S A route ((GeneralPaperSequentialLayout.run model S A start (schema model S A route)).1 ++ rest)).remaining = rest ∧
      Safe (GeneralPaperSequentialLayout.run model S A start (schema model S A route)).1 (GeneralPaperRouteFieldCursor.expected model S A route start) := by
    intro route start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperRouteFieldCursor.success model S A start route rest
    exact ⟨hv,hr,hs⟩
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,expected,run] using
    GeneralPaperNestedArrayFieldCursor.success model S A (GeneralPaperRouteFieldCursor.run S A)
      (schema model S A) (GeneralPaperRouteFieldCursor.expected model S A) hParser start source.data.toList rest

theorem covered {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m)) :
    Covered (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source)).1
      (expected model S A start source) := by
  have hEach : ∀ route : GroupRoute m,∀ start,
      Covered (GeneralPaperSequentialLayout.run model S A start (schema model S A route)).1
        (GeneralPaperRouteFieldCursor.expected model S A route start) := by
    intro route start
    exact (GeneralPaperRouteFieldCursor.success model S A start route []).2.2.2
  have hBody := GeneralPaperFieldDirectoryPartition.children model S A (schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) hEach (start + A * (64 + source.data.toList.length)) source.data.toList
  have h := GeneralPaperFieldDirectoryPartition.compose A (GeneralPaperScalarArrayFieldCursor.layoutHeader A start source.data.toList.length) _ _ hBody
  change Covered (GeneralPaperSequentialLayout.run model S A start _).1 _
  rw [plan]
  simpa only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,
    GeneralPaperScalarArrayFieldCursor.layoutHeader,expected] using h

theorem root {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m)) :
    (expected model S A start source).root = GeneralPaperScalarArrayFieldCursor.layoutHeader A start n := by
  change GeneralPaperScalarArrayFieldCursor.layoutHeader A start source.data.toList.length = _
  rw [Array.length_toList,source.size]

end Blotto.GeneralPaperRouteArrayCursor
