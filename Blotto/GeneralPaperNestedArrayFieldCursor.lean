import Blotto.GeneralPaperChildDirectorySpecification

/-! A nested-array parser fixes each child parser, advances through actual
regions once, and installs its outer header targets in the temporary field
directory. Root-word copying is explicit. Specifications of schemas/expected
directories are proof observers, never execution inputs. -/
namespace Blotto.GeneralPaperNestedArrayFieldCursor
open GeneralPaperFieldDirectory GeneralPaperFieldDirectoryParsers GeneralPaperSequentialLayout
open GeneralPaperFieldDirectorySafety
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def rootWords (S A : ℕ) : List (Region A) → List (FixedBinaryWord A) × ℕ
  | [] => ([],64 * (S + A + 1))
  | root :: roots =>
    let later := rootWords S A roots
    (root.reference :: later.1,later.2 + A + 64 * (S + A + 1))

theorem root_words_data (S A : ℕ) (roots : List (Region A)) :
    (rootWords S A roots).1 = roots.map Region.reference := by
  induction roots with
  | nil => rfl
  | cons root roots ih => simp only [rootWords,ih,List.map_cons]

theorem root_words_work (S A : ℕ) (roots : List (Region A)) :
    (rootWords S A roots).2 = roots.length * (A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction roots with
  | nil => simp only [rootWords,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons root roots ih => simp only [rootWords,ih,List.length_cons]; ring

def compose {A : ℕ} (header : Region A) (body : Body A) : Directory A :=
  ⟨header,⟨header,64,body.roots.map Region.reference⟩ :: body.headers,body.cells⟩

def runList {α : Type*} (S A : ℕ) (parser : Parser α A) (values : List α) : List (Region A) → GeneralPaperFieldDirectoryParsers.Result A
  | [] => ⟨none,[],64 * (S + A + 1)⟩
  | header :: regions =>
    let children := GeneralPaperChildDirectoryCursor.run S A parser values regions
    match children.values with
    | none => ⟨none,children.remaining,children.work + GeneralPaperLastRegionSelection.price S A header + 64 * (S + A + 1)⟩
    | some body =>
      let references := rootWords S A body.roots
      ⟨some ⟨header,⟨header,64,references.1⟩ :: body.headers,body.cells⟩,children.remaining,
        children.work + references.2 + GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1)⟩

theorem compose_safe (A : ℕ) (header : Region A) (regions : List (Region A)) (body : Body A)
    (hBody : SafeBody regions body) (hLength : header.length = A * (64 + body.roots.length)) :
    Safe (header :: regions) (compose header body) := by
  refine ⟨List.mem_cons_self ..,?_,?_,?_,hBody.2.2.2.2⟩
  · change (header :: body.headers.map GeneralPaperReferenceRegionSlots.Header.region).Sublist (header :: regions)
    exact hBody.2.1.cons_cons header
  · exact hBody.2.2.1.cons header
  · intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · change A * (64 + (body.roots.map Region.reference).length) ≤ header.length
      rw [List.length_map,hLength]
    · exact hBody.2.2.2.1 h hh

theorem success {α : Type*} (model : RationalCostModel) (S A : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A)
    (hParser : ∀ value start rest,
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).values = some (expected value start) ∧
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).remaining = rest ∧
      Safe (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (expected value start))
    (start : ℕ) (values : List α) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start
      (A * (64 + values.length) :: (values.map schema).flatten)).1
    let header := GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length
    let body := GeneralPaperChildDirectorySpecification.collect
      (GeneralPaperChildDirectorySpecification.directories schema expected (start + A * (64 + values.length)) values)
    (runList S A parser values (regions ++ rest)).values = some (compose header body) ∧
      (runList S A parser values (regions ++ rest)).remaining = rest ∧ Safe regions (compose header body) := by
  dsimp only
  let header := GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length
  let next := start + A * (64 + values.length)
  let regions := (GeneralPaperSequentialLayout.run model S A next (values.map schema).flatten).1
  let body := GeneralPaperChildDirectorySpecification.collect
    (GeneralPaperChildDirectorySpecification.directories schema expected next values)
  have hBody := GeneralPaperChildDirectorySpecification.success model S A parser schema expected hParser next values rest
  change (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).values = some body ∧
    (GeneralPaperChildDirectoryCursor.run S A parser values (regions ++ rest)).remaining = rest ∧ SafeBody regions body at hBody
  have hCount := GeneralPaperChildDirectoryCursor.root_count S A parser values (regions ++ rest) body hBody.1
  have hRegions : (GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: (values.map schema).flatten)).1 =
      header :: regions := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header,regions,next,
      GeneralPaperScalarArrayFieldCursor.layoutHeader]
  have hParsed : (runList S A parser values (header :: (regions ++ rest))).values = some (compose header body) ∧
      (runList S A parser values (header :: (regions ++ rest))).remaining = rest := by
    simp only [runList,hBody.1,hBody.2.1,root_words_data,compose,and_self]
  have hSafe := compose_safe A header regions body hBody.2.2 (by change A * (64 + values.length) = _; rw [hCount])
  simpa only [hRegions,List.cons_append] using And.intro hParsed.1 (And.intro hParsed.2 hSafe)

end Blotto.GeneralPaperNestedArrayFieldCursor
