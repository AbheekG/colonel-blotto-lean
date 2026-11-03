import Blotto.GeneralPaperMappedCursorWork

/-! Price the actual forward child-directory loop. Schemas, expected
directories and component prices are erased proof parameters; the execution
still calls only its concrete child parser once per source value. Complete
child copying and per-child control are included in the joined price. -/
namespace Blotto.GeneralPaperChildCursorWork
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def Correct {α : Type*} (model : RationalCostModel) (S A : ℕ) (schema : α → List ℕ)
    (expected : α → ℕ → Directory A) (parser : Parser α A) : Prop :=
  ∀ value start rest,
    (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).values = some (expected value start) ∧
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).remaining = rest ∧
      Safe (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (expected value start)

def Price {α : Type*} (model : RationalCostModel) (S A C : ℕ) (schema : α → List ℕ) (parser : Parser α A) : Prop :=
  ∀ value start rest,start + (schema value).sum < 2 ^ A →
    (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).work ≤
      ((schema value).sum + 1) * C * unit model S A

theorem raise (model : RationalCostModel) (S A B C D work : ℕ)
    (h : work ≤ (B + 1) * C * unit model S A) (hCD : C ≤ D) :
    work ≤ (B + 1) * D * unit model S A :=
  h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCD))

theorem children_work {α : Type*} (model : RationalCostModel) (S A C : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (hParser : Correct model S A schema expected parser)
    (hPrice : Price model S A C schema parser)
    (hPos : ∀ value,∀ size ∈ schema value,0 < size)
    (hA : 0 < A) (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (values.map schema).flatten.sum < 2 ^ A) :
    (GeneralPaperChildDirectoryCursor.run S A parser values
      ((GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1 ++ rest)).work ≤
      ((values.map schema).flatten.sum + values.length + 1) * (C + 17) * unit model S A := by
  induction values generalizing start with
  | nil =>
    change 64 * (S + A + 1) ≤ (0 + 0 + 1) * (C + 17) * unit model S A
    have h := metadata model S A
    nlinarith only [h.2.1,Nat.zero_le (C * unit model S A)]
  | cons value values ih =>
    let first := (GeneralPaperSequentialLayout.run model S A start (schema value)).1
    let next := start + (schema value).sum
    let later := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1
    let head := expected value start
    let tail := GeneralPaperChildDirectorySpecification.collect
      (GeneralPaperChildDirectorySpecification.directories schema expected next values)
    have hTotal : start + ((schema value).sum + (values.map schema).flatten.sum) < 2 ^ A := by
      simpa only [List.map_cons,List.flatten_cons,List.sum_append] using hCap
    have hHeadCap : start + (schema value).sum < 2 ^ A := by omega
    have hTailCap : next + (values.map schema).flatten.sum < 2 ^ A := by dsimp only [next]; omega
    have hRegions : (GeneralPaperSequentialLayout.run model S A start ((value :: values).map schema).flatten).1 = first ++ later := by
      rw [List.map_cons,List.flatten_cons,GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
    have hHead := hParser value start (later ++ rest)
    change (parser value (first ++ (later ++ rest))).values = some head ∧
      (parser value (first ++ (later ++ rest))).remaining = later ++ rest ∧ Safe first head at hHead
    have hTail := GeneralPaperChildDirectorySpecification.success model S A parser schema expected hParser next values rest
    change (GeneralPaperChildDirectoryCursor.run S A parser values (later ++ rest)).values = some tail ∧
      (GeneralPaperChildDirectoryCursor.run S A parser values (later ++ rest)).remaining = rest ∧ SafeBody later tail at hTail
    have hTailValues : (GeneralPaperChildDirectoryCursor.run S A parser values
        (parser value (first ++ (later ++ rest))).remaining).values = some tail := by rw [hHead.2.1]; exact hTail.1
    have hStep := (GeneralPaperChildDirectoryCursor.step S A parser value values
      (first ++ (later ++ rest)) head tail hHead.1 hTailValues).2.2
    rw [hHead.2.1] at hStep
    have hHeadPrice := hPrice value start (later ++ rest) hHeadCap
    change (parser value (first ++ (later ++ rest))).work ≤ ((schema value).sum + 1) * C * unit model S A at hHeadPrice
    have hTailPrice := ih next hTailCap
    change (GeneralPaperChildDirectoryCursor.run S A parser values (later ++ rest)).work ≤
      ((values.map schema).flatten.sum + values.length + 1) * (C + 17) * unit model S A at hTailPrice
    have hCopy := prepend_work model S A start (⟨schema value,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) head tail
      hHead.2.2 (hPos value) hA hHeadCap
    change (prepend S A head tail).2 ≤ ((schema value).sum + 1) * 16 * unit model S A at hCopy
    have hMeta := metadata model S A
    rw [hRegions,List.append_assoc,hStep]
    simp only [List.map_cons,List.flatten_cons,List.sum_append,List.length_cons]
    nlinarith only [hHeadPrice,hTailPrice,hCopy,hMeta.2.1,Nat.zero_le ((schema value).sum * unit model S A)]

theorem root_words_work (model : RationalCostModel) (S A : ℕ) (roots : List (Region A)) :
    (GeneralPaperNestedArrayFieldCursor.rootWords S A roots).2 ≤ (roots.length + 1) * unit model S A := by
  rw [GeneralPaperNestedArrayFieldCursor.root_words_work]
  have hStep : A + 64 * (S + A + 1) ≤ unit model S A := by unfold unit; omega
  have h := Nat.mul_le_mul_left roots.length hStep
  have hMeta := metadata model S A
  nlinarith only [h,hMeta.2.1]

end Blotto.GeneralPaperChildCursorWork
