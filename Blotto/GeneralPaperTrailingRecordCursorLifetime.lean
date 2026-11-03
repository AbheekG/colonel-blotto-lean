import Blotto.GeneralPaperMatrixCursorLifetime

/-! Complete lifetime for the existing trailing-directory-record cursor.
The child loop sees the actual record suffix. Header append copies its left
list only; its recursive frames coexist with assembly and partial prices. -/
namespace Blotto.GeneralPaperTrailingRecordCursorLifetime
open GeneralPaperFieldDirectory (Directory Body)
open GeneralPaperSequentialLayout (Region)
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperChildCursorWork (Correct)
open GeneralPaperChildDirectoryLifetime (Lifetime)
open GeneralPaperChildDirectorySpecification (collect directories)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def body {α : Type*} {A : ℕ} (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (start : ℕ) (values : List α) : Body A := collect (directories schema expected start values)

def record {α : Type*} (A start arity : ℕ) (schema : α → List ℕ) (values : List α) : Region A :=
  GeneralPaperTrailingScalarRecord.header A (start + (values.map schema).flatten.sum) arity

def stream {α : Type*} (model : RationalCostModel) (S A start arity : ℕ) (schema : α → List ℕ)
    (values : List α) (rest : List (Region A)) : List (Region A) :=
  (GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1 ++ record A start arity schema values :: rest

def price {α : Type*} (model : RationalCostModel) (S A start arity : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (values : List α) (rest : List (Region A)) : ℕ :=
  (GeneralPaperTrailingDirectoryRecord.run S A parser values (stream model S A start arity schema values rest)).work

def controls (S A childWork rootWork appendWork readWork totalWork : ℕ) : List ℕ :=
  [S,A,appendWork,childWork + rootWork,childWork + rootWork + appendWork,
    childWork + rootWork + appendWork + readWork,totalWork]

def window {α : Type*} (model : RationalCostModel) (S A start arity : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (values : List α) (rest : List (Region A)) : ℕ :=
  let actual := body schema expected start values
  let region := record A start arity schema values
  let childWork := (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A start arity schema values rest)).work
  let rootWork := (GeneralPaperNestedArrayFieldCursor.rootWords S A actual.roots).2
  let appendWork := (GeneralPaperFieldDirectory.appendHeaders S A actual.headers
    [GeneralPaperDirectoryRecordAssemblyLifetime.header region 0 actual]).2
  let total := price model S A start arity parser schema values rest
  GeneralPaperDirectoryRecordAssemblyLifetime.window S A 0 region actual
      (GeneralPaperChildDirectoryLifetime.window model S A parser schema expected space start values (region :: rest)) childWork total +
    GeneralPaperDirectoryAppendLifetime.headerFrames S A actual.headers [GeneralPaperDirectoryRecordAssemblyLifetime.header region 0 actual] +
    fields S (controls S A childWork rootWork appendWork (GeneralPaperLastRegionSelection.price S A region) total) + 64 * S

theorem layout_stream {α : Type*} (model : RationalCostModel) (S A start arity : ℕ) (schema : α → List ℕ)
    (values : List α) (rest : List (Region A)) :
    (GeneralPaperSequentialLayout.run model S A start ((values.map schema).flatten ++ [A * arity])).1 ++ rest =
      stream model S A start arity schema values rest := by
  rw [GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
  simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,stream,record,
    GeneralPaperTrailingScalarRecord.header,List.append_assoc,List.singleton_append]

theorem window_bound {α : Type*} (model : RationalCostModel) (S A C Q : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A C schema parser space)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start arity : ℕ) (values : List α) (rest : List (Region A)) (hArity : values.length ≤ arity)
    (hCap : start + ((values.map schema).flatten.sum + A * arity) < 2 ^ A)
    (hWork : (GeneralPaperTrailingDirectoryRecord.run S A parser values
      ((GeneralPaperSequentialLayout.run model S A start ((values.map schema).flatten ++ [A * arity])).1 ++ rest)).work ≤ Q) :
    window model S A start arity parser schema expected space values rest ≤
      ((values.map schema).flatten.sum + A * arity + 1) * (C + 96) * unit model S A Q := by
  let actual := body schema expected start values
  let region := record A start arity schema values
  let childWork := (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A start arity schema values rest)).work
  let rootWork := (GeneralPaperNestedArrayFieldCursor.rootWords S A actual.roots).2
  let appendWork := (GeneralPaperFieldDirectory.appendHeaders S A actual.headers
    [GeneralPaperDirectoryRecordAssemblyLifetime.header region 0 actual]).2
  let readWork := GeneralPaperLastRegionSelection.price S A region
  let total := price model S A start arity parser schema values rest
  rw [layout_stream] at hWork
  change total ≤ Q at hWork
  have hFirstCap : start + (values.map schema).flatten.sum < 2 ^ A := by omega
  have hSuccess := GeneralPaperChildDirectorySpecification.success model S A parser schema expected hCorrect start values (region :: rest)
  change (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A start arity schema values rest)).values = some actual ∧
    (GeneralPaperChildDirectoryCursor.run S A parser values (stream model S A start arity schema values rest)).remaining = region :: rest ∧
    GeneralPaperFieldDirectorySafety.SafeBody (GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1 actual at hSuccess
  have hRun := (GeneralPaperTrailingDirectoryRecord.on_children S A parser values _ actual region rest hSuccess.1 hSuccess.2.1).2.2
  change total = childWork + rootWork + appendWork + readWork + 128 * (S + A + 1) at hRun
  have hCount : actual.roots.length = values.length := by
    simp only [actual,body,collect,List.length_map,GeneralPaperChildDirectorySpecification.directory_count]
  have hPosFlat : GeneralPaperMeasuredPlanPositive.Positive (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) := by
    intro size hs
    obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp hs
    obtain ⟨value,_,rfl⟩ := List.mem_map.mp hSizes
    exact hPos value size hSize
  have hChildren := GeneralPaperChildDirectoryLifetime.window_bound model S A C Q parser schema expected space
    hCorrect hLife hPos hA start values (region :: rest) hFirstCap (by change childWork ≤ Q; omega)
  have hBody := GeneralPaperDirectoryBodyStorage.body_bound model S A start
    (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) actual hSuccess.2.2 hPosFlat hA hFirstCap
  rw [hCount] at hBody
  change GeneralPaperDirectoryPrependLifetime.bodyFoot S actual ≤
    ((values.map schema).flatten.sum + values.length + 1) * 4096 * (S + A + 1) at hBody
  have hBodyPay := Nat.mul_le_mul_left ((values.map schema).flatten.sum + values.length + 1)
    (GeneralPaperChildDirectoryLifetime.metadata_bound model S A Q)
  have hBodyBound : GeneralPaperDirectoryPrependLifetime.bodyFoot S actual ≤
      ((values.map schema).flatten.sum + values.length + 1) * unit model S A Q := by nlinarith only [hBody,hBodyPay]
  have hRange := GeneralPaperSequentialLayout.range model S A start (values.map schema).flatten
  have hRoots : ∀ root ∈ actual.roots,root.stop < 2 ^ A :=
    fun root hr => (hRange root (hSuccess.2.2.1 root hr)).2.trans_lt hFirstCap
  have hRegion : region.stop < 2 ^ A := by change start + (values.map schema).flatten.sum + A * arity < 2 ^ A; omega
  have hHeader : A * (0 + actual.roots.length) ≤ region.length := by
    change A * (0 + actual.roots.length) ≤ A * arity
    rw [hCount,Nat.zero_add]
    exact Nat.mul_le_mul_left A hArity
  have hAssembly := GeneralPaperDirectoryRecordAssemblyLifetime.window_bound model S A Q
    (values.map schema).flatten.sum values.length (C + 48) 0 region actual
    (GeneralPaperChildDirectoryLifetime.window model S A parser schema expected space start values (region :: rest)) childWork total
    hA hRoots hRegion hHeader hCount hChildren hBodyBound hWork (by change childWork + rootWork + readWork ≤ total; omega)
  have hHeaderCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start
    (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) actual.headers hSuccess.2.2.2.1 hFirstCap
  have hFrames := GeneralPaperDirectoryAppendLifetime.header_frames_bound model S A Q actual.headers
    [GeneralPaperDirectoryRecordAssemblyLifetime.header region 0 actual] hA hSuccess.2.2.2.2.2.1 hHeaderCaps
    (by change appendWork ≤ Q; omega)
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start
    (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) actual.headers hSuccess.2.2.2.1 hA hSuccess.2.2.2.2.2.1
  have hHeaders := hSuccess.2.2.2.1.length_le
  rw [List.length_map,GeneralPaperSequentialLayout.count] at hHeaders
  have hBlocks := GeneralPaperMeasuredPlanPositive.block_count _ hPosFlat
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A childWork rootWork appendWork readWork total) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 7 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S (controls S A childWork rootWork appendWork readWork total) + 64 * S ≤ unit model S A Q := by omega
  have hN : values.length ≤ A * arity := hArity.trans (Nat.le_mul_of_pos_left arity hA)
  have hMass := Nat.mul_le_mul_right ((C + 48 + 12) * unit model S A Q)
    (show (values.map schema).flatten.sum + values.length + 1 ≤ (values.map schema).flatten.sum + A * arity + 1 by omega)
  have hFrameMass := Nat.mul_le_mul_right (12 * unit model S A Q)
    (show GeneralPaperReferenceHeaderSlotArea.slots actual.headers + actual.headers.length + 1 ≤
      2 * ((values.map schema).flatten.sum + A * arity + 1) by change _ ≤ (values.map schema).flatten.sum at hSlots; change (values.map schema).flatten.length ≤ (values.map schema).flatten.sum at hBlocks; omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ (values.map schema).flatten.sum + A * arity + 1 by omega)
  change window model S A start arity parser schema expected space values rest ≤ _
  dsimp only [window]
  nlinarith only [hAssembly,hMass,hFrames,hFrameMass,hParent,hBase]

end Blotto.GeneralPaperTrailingRecordCursorLifetime
