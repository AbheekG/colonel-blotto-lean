import Blotto.GeneralPaperDirectoryRecordAssemblyLifetime

/-! Complete front-record/nested-array composition on actual region
streams. The successful price below is an erased observer equal to the
existing parsers' recorded price, not an execution input. All child/body,
root-word, header/read and enclosing price owners coexist. -/
namespace Blotto.GeneralPaperFrontRecordCursorLifetime
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperSequentialLayout (Region)
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperChildCursorWork (Correct)
open GeneralPaperChildDirectoryLifetime (Lifetime)
open GeneralPaperChildDirectorySpecification (collect directories)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def body {α : Type*} {A : ℕ} (fixed stride : ℕ) (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (start : ℕ) (values : List α) : GeneralPaperFieldDirectory.Body A :=
  collect (directories schema expected (start + A * (stride * values.length + fixed)) values)

def stream {α : Type*} (model : RationalCostModel) (S A fixed stride : ℕ) (schema : α → List ℕ)
    (start : ℕ) (values : List α) (rest : List (Region A)) : List (Region A) :=
  (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map schema).flatten).1 ++ rest

def price {α : Type*} (model : RationalCostModel) (S A fixed stride : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (start : ℕ) (values : List α) (rest : List (Region A)) : ℕ :=
  (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A fixed stride schema start values rest)).work +
    (GeneralPaperNestedArrayFieldCursor.rootWords S A (body fixed stride schema expected start values).roots).2 +
    GeneralPaperLastRegionSelection.price S A (GeneralPaperScalarRecordComponents.listHeader A start fixed stride values.length) + 128 * (S + A + 1)

def window {α : Type*} (model : RationalCostModel) (S A fixed stride : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (start : ℕ) (values : List α) (rest : List (Region A)) : ℕ :=
  GeneralPaperDirectoryRecordAssemblyLifetime.window S A fixed (GeneralPaperScalarRecordComponents.listHeader A start fixed stride values.length)
    (body fixed stride schema expected start values)
    (GeneralPaperChildDirectoryLifetime.window model S A parser schema expected space (start + A * (stride * values.length + fixed)) values rest)
    (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A fixed stride schema start values rest)).work
    (price model S A fixed stride parser schema expected start values rest)

theorem generic_bound {α : Type*} (model : RationalCostModel) (S A fixed stride C Q : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A C schema parser space)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A) (hStride : 0 < stride)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (A * (stride * values.length + fixed) + (values.map schema).flatten.sum) < 2 ^ A)
    (hWork : price model S A fixed stride parser schema expected start values rest ≤ Q) :
    window model S A fixed stride parser schema expected space start values rest ≤
      (A * (stride * values.length + fixed) + (values.map schema).flatten.sum + 1) * (C + 64) * unit model S A Q := by
  let next := start + A * (stride * values.length + fixed)
  let actual := body fixed stride schema expected start values
  let region := GeneralPaperScalarRecordComponents.listHeader A start fixed stride values.length
  have hFirstCap : next + (values.map schema).flatten.sum < 2 ^ A := by dsimp only [next]; omega
  have hSafe := (GeneralPaperChildDirectorySpecification.success model S A parser schema expected hCorrect next values rest).2.2
  change GeneralPaperFieldDirectorySafety.SafeBody (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1 actual at hSafe
  have hCount : actual.roots.length = values.length := by
    simp only [actual,body,collect,List.length_map,GeneralPaperChildDirectorySpecification.directory_count]
  have hChildWork : (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A fixed stride schema start values rest)).work ≤ Q := by
    have h := hWork
    dsimp only [price] at h
    omega
  have hChildren := GeneralPaperChildDirectoryLifetime.window_bound model S A C Q parser schema expected space hCorrect hLife hPos hA next values rest hFirstCap hChildWork
  have hPlanPos : GeneralPaperMeasuredPlanPositive.Positive (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) := by
    intro size hs
    obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp hs
    obtain ⟨value,_,rfl⟩ := List.mem_map.mp hSizes
    exact hPos value size hSize
  have hBody := GeneralPaperDirectoryBodyStorage.body_bound model S A next (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan)
    actual hSafe hPlanPos hA hFirstCap
  rw [hCount] at hBody
  change GeneralPaperDirectoryPrependLifetime.bodyFoot S actual ≤
    ((values.map schema).flatten.sum + values.length + 1) * 4096 * (S + A + 1) at hBody
  have hBodyPay := Nat.mul_le_mul_left ((values.map schema).flatten.sum + values.length + 1)
    (GeneralPaperChildDirectoryLifetime.metadata_bound model S A Q)
  have hBodyBound : GeneralPaperDirectoryPrependLifetime.bodyFoot S actual ≤
      ((values.map schema).flatten.sum + values.length + 1) * unit model S A Q := by
    nlinarith only [hBody,hBodyPay]
  have hRange := GeneralPaperSequentialLayout.range model S A next (values.map schema).flatten
  have hRoots : ∀ root ∈ actual.roots,root.stop < 2 ^ A :=
    fun root hr => (hRange root (hSafe.1 root hr)).2.trans_lt hFirstCap
  have hHeader : A * (fixed + actual.roots.length) ≤ region.length := by
    rw [hCount]
    have hN := Nat.mul_le_mul_right values.length hStride
    change A * (fixed + values.length) ≤ A * (stride * values.length + fixed)
    exact Nat.mul_le_mul_left A (by omega)
  have hPrices : (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A fixed stride schema start values rest)).work +
      (GeneralPaperNestedArrayFieldCursor.rootWords S A actual.roots).2 + GeneralPaperLastRegionSelection.price S A region ≤
      price model S A fixed stride parser schema expected start values rest := by
    change _ ≤ (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A fixed stride schema start values rest)).work +
      (GeneralPaperNestedArrayFieldCursor.rootWords S A actual.roots).2 + GeneralPaperLastRegionSelection.price S A region + 128 * (S + A + 1)
    omega
  have hAssembly := GeneralPaperDirectoryRecordAssemblyLifetime.window_bound model S A Q
    (values.map schema).flatten.sum values.length (C + 48) fixed region actual
    (GeneralPaperChildDirectoryLifetime.window model S A parser schema expected space next values rest)
    (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A fixed stride schema start values rest)).work
    (price model S A fixed stride parser schema expected start values rest) hA hRoots
    (by change start + A * (stride * values.length + fixed) < 2 ^ A; omega) hHeader hCount hChildren hBodyBound hWork hPrices
  have hN : values.length ≤ A * (stride * values.length + fixed) := by
    have hs := Nat.mul_le_mul_right values.length hStride
    have ha := Nat.mul_le_mul_right (stride * values.length + fixed) hA
    nlinarith only [hs,ha]
  have hMass := Nat.mul_le_mul_right ((C + 48 + 12) * unit model S A Q)
    (show (values.map schema).flatten.sum + values.length + 1 ≤ A * (stride * values.length + fixed) + (values.map schema).flatten.sum + 1 by omega)
  have hCoefficient := Nat.mul_le_mul_left ((A * (stride * values.length + fixed) + (values.map schema).flatten.sum + 1) * unit model S A Q)
    (show C + 48 + 12 ≤ C + 64 by omega)
  change window model S A fixed stride parser schema expected space start values rest ≤
    ((values.map schema).flatten.sum + values.length + 1) * (C + 48 + 12) * unit model S A Q at hAssembly
  nlinarith only [hAssembly,hMass,hCoefficient]

theorem array_bound {α : Type*} (model : RationalCostModel) (S A C Q : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A C schema parser space)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (A * (64 + values.length) + (values.map schema).flatten.sum) < 2 ^ A)
    (hWork : (GeneralPaperNestedArrayFieldCursor.runList S A parser values
      ((GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: (values.map schema).flatten)).1 ++ rest)).work ≤ Q) :
    window model S A 64 1 parser schema expected space start values rest ≤
      (A * (64 + values.length) + (values.map schema).flatten.sum + 1) * (C + 64) * unit model S A Q := by
  have hBody := (GeneralPaperChildDirectorySpecification.success model S A parser schema expected hCorrect
    (start + A * (64 + values.length)) values rest).1
  have hRegions : (GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: (values.map schema).flatten)).1 =
      GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length ::
        (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map schema).flatten).1 := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,GeneralPaperScalarArrayFieldCursor.layoutHeader]
  rw [hRegions,List.cons_append] at hWork
  simp only [GeneralPaperNestedArrayFieldCursor.runList,hBody] at hWork
  have hCap' : start + (A * (1 * values.length + 64) + (values.map schema).flatten.sum) < 2 ^ A := by
    simpa only [Nat.one_mul,Nat.add_comm values.length 64] using hCap
  have hPrice : price model S A 64 1 parser schema expected start values rest ≤ Q := by
    simpa only [price,stream,body,Nat.one_mul,Nat.add_comm values.length 64,GeneralPaperScalarRecordComponents.listHeader,
      GeneralPaperScalarArrayFieldCursor.layoutHeader] using hWork
  have h := generic_bound model S A 64 1 C Q parser schema expected space hCorrect hLife hPos hA (by decide) start values rest hCap' hPrice
  simpa only [Nat.one_mul,Nat.add_comm values.length 64] using h

theorem list_bound {α : Type*} (model : RationalCostModel) (S A C Q : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A C schema parser space)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (A * (2 * values.length + 32) + (values.map schema).flatten.sum) < 2 ^ A)
    (hWork : (GeneralPaperFrontDirectoryList.run S A parser values
      ((GeneralPaperSequentialLayout.run model S A start (A * (2 * values.length + 32) :: (values.map schema).flatten)).1 ++ rest)).work ≤ Q) :
    window model S A 32 2 parser schema expected space start values rest ≤
      (A * (2 * values.length + 32) + (values.map schema).flatten.sum + 1) * (C + 64) * unit model S A Q := by
  have hBody := (GeneralPaperChildDirectorySpecification.success model S A parser schema expected hCorrect
    (start + A * (2 * values.length + 32)) values rest).1
  have hRegions : (GeneralPaperSequentialLayout.run model S A start (A * (2 * values.length + 32) :: (values.map schema).flatten)).1 =
      GeneralPaperScalarRecordComponents.listHeader A start 32 2 values.length ::
        (GeneralPaperSequentialLayout.run model S A (start + A * (2 * values.length + 32)) (values.map schema).flatten).1 := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,GeneralPaperScalarRecordComponents.listHeader]
  rw [hRegions,List.cons_append] at hWork
  simp only [GeneralPaperFrontDirectoryList.run,hBody] at hWork
  exact generic_bound model S A 32 2 C Q parser schema expected space hCorrect hLife hPos hA (by decide) start values rest hCap hWork

end Blotto.GeneralPaperFrontRecordCursorLifetime
