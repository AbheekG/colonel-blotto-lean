import Blotto.GeneralPaperChildCursorWork

/-! Complete actual enclosing array and trailing-record cursor work.
Reserved header area pays for child-loop margins; target construction and
directory-header copying are included. Component correctness/prices remain
erased premises that concrete source cursors discharge. -/
namespace Blotto.GeneralPaperRecordCursorWork
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork GeneralPaperChildCursorWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem nested {α : Type*} (model : RationalCostModel) (S A C : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (hParser : Correct model S A schema expected parser) (hPrice : Price model S A C schema parser)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (A * (64 + values.length) + (values.map schema).flatten.sum) < 2 ^ A) :
    (GeneralPaperNestedArrayFieldCursor.runList S A parser values
      ((GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: (values.map schema).flatten)).1 ++ rest)).work ≤
      (A * (64 + values.length) + (values.map schema).flatten.sum + 1) * (C + 24) * unit model S A := by
  let header := GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length
  let next := start + A * (64 + values.length)
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
  have hHeader := region_work model S A header hA (by change start + A * (64 + values.length) < 2 ^ A; omega)
  have hN : values.length ≤ A * (64 + values.length) := by
    have h := Nat.mul_le_mul_right (64 + values.length) hA
    nlinarith only [h]
  have hWhole := Nat.mul_le_mul_right ((C + 17) * unit model S A)
    (show (values.map schema).flatten.sum + values.length + 1 ≤ A * (64 + values.length) + (values.map schema).flatten.sum + 1 by omega)
  have hTargets := Nat.mul_le_mul_right (unit model S A)
    (show values.length + 1 ≤ A * (64 + values.length) + (values.map schema).flatten.sum + 1 by omega)
  have hSlack := Nat.mul_le_mul_right (unit model S A)
    (show 2 ≤ 6 * (A * (64 + values.length) + (values.map schema).flatten.sum + 1) by omega)
  have hMeta := metadata model S A
  have hRegions : (GeneralPaperSequentialLayout.run model S A start
      (A * (64 + values.length) :: (values.map schema).flatten)).1 = header :: regions := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header,regions,next,
      GeneralPaperScalarArrayFieldCursor.layoutHeader]
  rw [hRegions,List.cons_append]
  simp only [GeneralPaperNestedArrayFieldCursor.runList,hBody.1]
  nlinarith only [hChildren,hWords,hHeader,hWhole,hTargets,hSlack,hMeta.2.1]

theorem trailing {α : Type*} (model : RationalCostModel) (S A C : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (hParser : Correct model S A schema expected parser) (hPrice : Price model S A C schema parser)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start arity : ℕ) (values : List α) (rest : List (Region A)) (hArity : values.length ≤ arity)
    (hCap : start + ((values.map schema).flatten.sum + A * arity) < 2 ^ A) :
    (GeneralPaperTrailingDirectoryRecord.run S A parser values
      ((GeneralPaperSequentialLayout.run model S A start ((values.map schema).flatten ++ [A * arity])).1 ++ rest)).work ≤
      ((values.map schema).flatten.sum + A * arity + 1) * (C + 32) * unit model S A := by
  let first := (GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1
  let record := GeneralPaperTrailingScalarRecord.header A (start + (values.map schema).flatten.sum) arity
  let body := GeneralPaperChildDirectorySpecification.collect
    (GeneralPaperChildDirectorySpecification.directories schema expected start values)
  have hFirstCap : start + (values.map schema).flatten.sum < 2 ^ A := by omega
  have hBody := GeneralPaperChildDirectorySpecification.success model S A parser schema expected hParser start values (record :: rest)
  change (GeneralPaperChildDirectoryCursor.run S A parser values (first ++ record :: rest)).values = some body ∧
    (GeneralPaperChildDirectoryCursor.run S A parser values (first ++ record :: rest)).remaining = record :: rest ∧ SafeBody first body at hBody
  have hSafe : SafeBody first body := hBody.2.2
  have hCount := GeneralPaperChildDirectoryCursor.root_count S A parser values (first ++ record :: rest) body hBody.1
  have hChildren := children_work model S A C parser schema expected hParser hPrice hPos hA start values (record :: rest) hFirstCap
  change (GeneralPaperChildDirectoryCursor.run S A parser values (first ++ record :: rest)).work ≤ _ at hChildren
  have hWords := root_words_work model S A body.roots
  rw [hCount] at hWords
  have hPosFlat : GeneralPaperMeasuredPlanPositive.Positive (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) := by
    intro size hs
    obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp hs
    obtain ⟨value,_,rfl⟩ := List.mem_map.mp hSizes
    exact hPos value size hSize
  have hCopy := headers_layout_work model S A start (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan)
    body.headers [⟨record,0,body.roots.map Region.reference⟩] hSafe.2.1 hSafe.2.2.2.1 hPosFlat hA hFirstCap
  change (appendHeaders S A body.headers [⟨record,0,body.roots.map Region.reference⟩]).2 ≤
    ((values.map schema).flatten.sum + 1) * 8 * unit model S A at hCopy
  have hRecord := region_work model S A record hA (by change start + (values.map schema).flatten.sum + A * arity < 2 ^ A; omega)
  have hN : values.length ≤ A * arity := by
    have h := Nat.mul_le_mul_right arity hA
    nlinarith only [h,hArity]
  have hWhole := Nat.mul_le_mul_right ((C + 17) * unit model S A)
    (show (values.map schema).flatten.sum + values.length + 1 ≤ (values.map schema).flatten.sum + A * arity + 1 by omega)
  have hTargets := Nat.mul_le_mul_right (unit model S A)
    (show values.length + 1 ≤ (values.map schema).flatten.sum + A * arity + 1 by omega)
  have hCopies := Nat.mul_le_mul_right (8 * unit model S A)
    (show (values.map schema).flatten.sum + 1 ≤ (values.map schema).flatten.sum + A * arity + 1 by omega)
  have hSlack := Nat.mul_le_mul_right (unit model S A)
    (show 2 ≤ 6 * ((values.map schema).flatten.sum + A * arity + 1) by omega)
  have hMeta := metadata model S A
  have hRegions : (GeneralPaperSequentialLayout.run model S A start ((values.map schema).flatten ++ [A * arity])).1 = first ++ [record] := by
    rw [GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,first,record,GeneralPaperTrailingScalarRecord.header]
  have hRun := (GeneralPaperTrailingDirectoryRecord.on_children S A parser values (first ++ record :: rest) body record rest hBody.1 hBody.2.1).2.2
  rw [hRegions,List.append_assoc,List.singleton_append,hRun]
  nlinarith only [hChildren,hWords,hCopy,hRecord,hWhole,hTargets,hCopies,hSlack,hMeta.2.1]

end Blotto.GeneralPaperRecordCursorWork
