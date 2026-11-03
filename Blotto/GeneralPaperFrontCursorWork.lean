import Blotto.GeneralPaperPreparedCursorWorkRates

/-! Complete front-list directory extraction. The actual two-word-per-child
header pays for every child-loop margin, root copy and enclosing control.
Component schemas and prices remain erased theorem premises. -/
namespace Blotto.GeneralPaperFrontCursorWork
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork GeneralPaperChildCursorWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem front {α : Type*} (model : RationalCostModel) (S A C : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (hParser : Correct model S A schema expected parser) (hPrice : Price model S A C schema parser)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (A * (2 * values.length + 32) + (values.map schema).flatten.sum) < 2 ^ A) :
    (GeneralPaperFrontDirectoryList.run S A parser values
      ((GeneralPaperSequentialLayout.run model S A start (A * (2 * values.length + 32) :: (values.map schema).flatten)).1 ++ rest)).work ≤
      (A * (2 * values.length + 32) + (values.map schema).flatten.sum + 1) * (C + 24) * unit model S A := by
  let header := GeneralPaperScalarRecordComponents.listHeader A start 32 2 values.length
  let next := start + A * (2 * values.length + 32)
  let regions := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1
  let body := GeneralPaperChildDirectorySpecification.collect
    (GeneralPaperChildDirectorySpecification.directories schema expected next values)
  have hInnerCap : next + (values.map schema).flatten.sum < 2 ^ A := by dsimp only [next]; omega
  have hBody := GeneralPaperChildDirectorySpecification.success model S A parser schema expected hParser next values rest
  change (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).values = some body ∧
    (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).remaining = rest ∧ SafeBody regions body at hBody
  have hCount := GeneralPaperChildDirectoryCursor.root_count S A parser values (regions ++ rest) body hBody.1
  have hChildren := children_work model S A C parser schema expected hParser hPrice hPos hA next values rest hInnerCap
  change (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).work ≤ _ at hChildren
  have hWords := root_words_work model S A body.roots
  rw [hCount] at hWords
  have hHeader := region_work model S A header hA (by change start + A * (2 * values.length + 32) < 2 ^ A; omega)
  have hN : values.length ≤ A * (2 * values.length + 32) := by
    have h := Nat.mul_le_mul_right (2 * values.length + 32) hA
    nlinarith only [h]
  have hWhole := Nat.mul_le_mul_right ((C + 17) * unit model S A)
    (show (values.map schema).flatten.sum + values.length + 1 ≤ A * (2 * values.length + 32) + (values.map schema).flatten.sum + 1 by omega)
  have hTargets := Nat.mul_le_mul_right (unit model S A)
    (show values.length + 1 ≤ A * (2 * values.length + 32) + (values.map schema).flatten.sum + 1 by omega)
  have hSlack := Nat.mul_le_mul_right (unit model S A)
    (show 2 ≤ 6 * (A * (2 * values.length + 32) + (values.map schema).flatten.sum + 1) by omega)
  have hMeta := metadata model S A
  have hRegions : (GeneralPaperSequentialLayout.run model S A start
      (A * (2 * values.length + 32) :: (values.map schema).flatten)).1 = header :: regions := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header,regions,next,
      GeneralPaperScalarRecordComponents.listHeader]
  rw [hRegions,List.cons_append]
  simp only [GeneralPaperFrontDirectoryList.run,hBody.1]
  nlinarith only [hChildren,hWords,hHeader,hWhole,hTargets,hSlack,hMeta.2.1]

end Blotto.GeneralPaperFrontCursorWork
