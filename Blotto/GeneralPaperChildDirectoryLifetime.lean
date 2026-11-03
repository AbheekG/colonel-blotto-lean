import Blotto.GeneralPaperDirectoryBodyStorage

/-! Actual forward child-directory frames compose complete concrete child
lifetimes with prepend-local lifetimes. Child output tails share one final
body owner. Schema/expected/space functions are erased proof observers;
execution still calls only the original parser on the actual region stream. -/
namespace Blotto.GeneralPaperChildDirectoryLifetime
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperSequentialLayout (Region)
open GeneralPaperChildDirectoryCursor (run)
open GeneralPaperChildDirectorySpecification (directories collect)
open GeneralPaperChildCursorWork (Correct)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem metadata_bound (model : RationalCostModel) (S A Q : ℕ) : 4096 * (S + A + 1) ≤ unit model S A Q := by
  unfold unit
  omega

def Lifetime {α : Type*} (model : RationalCostModel) (S A C : ℕ) (schema : α → List ℕ) (parser : Parser α A)
    (space : α → ℕ → List (Region A) → ℕ) : Prop :=
  ∀ value start rest Q,start + (schema value).sum < 2 ^ A →
    (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).work ≤ Q →
    space value start rest ≤ ((schema value).sum + 1) * C * unit model S A Q

def controls {α : Type*} (model : RationalCostModel) (S A : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (start : ℕ) (value : α) (values : List α) (rest : List (Region A)) : List ℕ :=
  let next := start + (schema value).sum
  let laterRegions := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1 ++ rest
  let firstRegions := (GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ laterRegions
  let childWork := (parser value firstRegions).work
  let tailWork := (run S A parser values laterRegions).work
  let appendWork := (GeneralPaperFieldDirectory.prepend S A (expected value start) (collect (directories schema expected next values))).2
  [S,A,childWork,tailWork,appendWork,childWork+tailWork,childWork+tailWork+appendWork,(run S A parser (value :: values) firstRegions).work]

def frames {α : Type*} (model : RationalCostModel) (S A : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ) : ℕ → List α → List (Region A) → ℕ
  | _,[],rest => fields S [S,A,(run S A parser [] rest).work] + 64 * S
  | start,value :: values,rest =>
    let next := start + (schema value).sum
    let laterRegions := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1 ++ rest
    space value start laterRegions +
      GeneralPaperDirectoryPrependLifetime.localWindow S A (expected value start) (collect (directories schema expected next values)) +
      fields S (controls model S A parser schema expected start value values rest) + 128 * S +
      frames model S A parser schema expected space next values rest

theorem frames_bound {α : Type*} (model : RationalCostModel) (S A C Q : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A C schema parser space)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (values.map schema).flatten.sum < 2 ^ A)
    (hWork : (run S A parser values ((GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1 ++ rest)).work ≤ Q) :
    frames model S A parser schema expected space start values rest ≤
      ((values.map schema).flatten.sum + values.length + 1) * (C + 44) * unit model S A Q := by
  induction values generalizing start with
  | nil =>
    have hWhole : (run S A parser [] rest).work ≤ Q := by
      simpa only [List.map_nil,List.flatten_nil,GeneralPaperSequentialLayout.run,List.nil_append] using hWork
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(run S A parser [] rest).work] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [frames,List.map_nil,List.flatten_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
    nlinarith only [hFields,hUnit,Nat.zero_le (C * unit model S A Q)]
  | cons value values ih =>
    let first := (GeneralPaperSequentialLayout.run model S A start (schema value)).1
    let next := start + (schema value).sum
    let later := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1
    let head := expected value start
    let tail := collect (directories schema expected next values)
    have hTotal : start + ((schema value).sum + (values.map schema).flatten.sum) < 2 ^ A := by
      simpa only [List.map_cons,List.flatten_cons,List.sum_append] using hCap
    have hHeadCap : start + (schema value).sum < 2 ^ A := by omega
    have hTailCap : next + (values.map schema).flatten.sum < 2 ^ A := by dsimp only [next]; omega
    have hRegions : (GeneralPaperSequentialLayout.run model S A start ((value :: values).map schema).flatten).1 = first ++ later := by
      rw [List.map_cons,List.flatten_cons,GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
    have hHead := hCorrect value start (later ++ rest)
    change (parser value (first ++ (later ++ rest))).values = some head ∧
      (parser value (first ++ (later ++ rest))).remaining = later ++ rest ∧ GeneralPaperFieldDirectorySafety.Safe first head at hHead
    have hTail := GeneralPaperChildDirectorySpecification.success model S A parser schema expected hCorrect next values rest
    change (run S A parser values (later ++ rest)).values = some tail ∧
      (run S A parser values (later ++ rest)).remaining = rest ∧ GeneralPaperFieldDirectorySafety.SafeBody later tail at hTail
    have hTailValues : (run S A parser values (parser value (first ++ (later ++ rest))).remaining).values = some tail := by
      rw [hHead.2.1]; exact hTail.1
    have hStep := (GeneralPaperChildDirectoryCursor.step S A parser value values (first ++ (later ++ rest)) head tail hHead.1 hTailValues).2.2
    rw [hHead.2.1] at hStep
    rw [hRegions,List.append_assoc,hStep] at hWork
    have hChild := hLife value start (later ++ rest) Q hHeadCap (by change (parser value (first ++ (later ++ rest))).work ≤ Q; omega)
    have hCopy := GeneralPaperDirectoryPrependLifetime.local_bound model S A start Q (⟨schema value,0⟩ : GeneralPaperMeasuredBlockPlan.Plan)
      head tail hHead.2.2 (hPos value) hA hHeadCap (by omega)
    change GeneralPaperDirectoryPrependLifetime.localWindow S A head tail ≤ ((schema value).sum + 1) * 40 * unit model S A Q at hCopy
    have ht := ih next hTailCap (by change (run S A parser values (later ++ rest)).work ≤ Q; omega)
    have hFields := fields_bound S (natBits (cap S A Q)) (controls model S A parser schema expected start value values rest) (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
      change x = S ∨ x = A ∨ x = (parser value (first ++ (later ++ rest))).work ∨
        x = (run S A parser values (later ++ rest)).work ∨ x = (GeneralPaperFieldDirectory.prepend S A head tail).2 ∨
        x = (parser value (first ++ (later ++ rest))).work + (run S A parser values (later ++ rest)).work ∨
        x = (parser value (first ++ (later ++ rest))).work + (run S A parser values (later ++ rest)).work +
          (GeneralPaperFieldDirectory.prepend S A head tail).2 ∨ x = (run S A parser (value :: values) (first ++ (later ++ rest))).work at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 8 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    have hParent : fields S (controls model S A parser schema expected start value values rest) + 128 * S ≤ unit model S A Q := by omega
    simp only [frames,List.map_cons,List.flatten_cons,List.sum_append,List.length_cons]
    change space value start (later ++ rest) + GeneralPaperDirectoryPrependLifetime.localWindow S A head tail +
      fields S (controls model S A parser schema expected start value values rest) + 128 * S +
      frames model S A parser schema expected space next values rest ≤ _
    nlinarith only [hChild,hCopy,ht,hParent,Nat.zero_le ((schema value).sum * unit model S A Q)]

def window {α : Type*} (model : RationalCostModel) (S A : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (start : ℕ) (values : List α) (rest : List (Region A)) : ℕ :=
  GeneralPaperDirectoryPrependLifetime.bodyFoot S (collect (directories schema expected start values)) +
    frames model S A parser schema expected space start values rest

theorem window_bound {α : Type*} (model : RationalCostModel) (S A C Q : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A C schema parser space)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (values.map schema).flatten.sum < 2 ^ A)
    (hWork : (run S A parser values ((GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1 ++ rest)).work ≤ Q) :
    window model S A parser schema expected space start values rest ≤
      ((values.map schema).flatten.sum + values.length + 1) * (C + 48) * unit model S A Q := by
  have hFrames := frames_bound model S A C Q parser schema expected space hCorrect hLife hPos hA start values rest hCap hWork
  have hSafe := (GeneralPaperChildDirectorySpecification.success model S A parser schema expected hCorrect start values rest).2.2
  have hPlanPos : GeneralPaperMeasuredPlanPositive.Positive (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) := by
    intro size hs
    obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp hs
    obtain ⟨value,_,rfl⟩ := List.mem_map.mp hSizes
    exact hPos value size hSize
  have hBody := GeneralPaperDirectoryBodyStorage.body_bound model S A start (⟨(values.map schema).flatten,0⟩ : GeneralPaperMeasuredBlockPlan.Plan)
    (collect (directories schema expected start values)) hSafe hPlanPos hA hCap
  have hCount : (collect (directories schema expected start values)).roots.length = values.length := by
    simp only [collect,List.length_map,GeneralPaperChildDirectorySpecification.directory_count]
  rw [hCount] at hBody
  change GeneralPaperDirectoryPrependLifetime.bodyFoot S _ ≤ GeneralPaperDirectoryBodyStorage.bound S A (values.map schema).flatten.sum values.length at hBody
  have hUnitMeta := metadata_bound model S A Q
  have hFactor := Nat.mul_le_mul_left ((values.map schema).flatten.sum + values.length + 1)
    hUnitMeta
  unfold GeneralPaperDirectoryBodyStorage.bound at hBody
  unfold window
  nlinarith only [hFrames,hBody,hFactor]

end Blotto.GeneralPaperChildDirectoryLifetime
