import Blotto.GeneralPaperRouteArrayInstallation

/-! Heterogeneous child fields followed by their existing reserved record.
Concrete callers fix the child parser and field tags. Schemas and expected
directories occur only in the erased compositional correctness theorem. -/
namespace Blotto.GeneralPaperTrailingDirectoryRecord
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperReferenceRegionSlots (Header)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def compose {A : ℕ} (record : Region A) (body : Body A) : Directory A :=
  ⟨record,body.headers ++ [⟨record,0,body.roots.map Region.reference⟩],body.cells⟩

def run {α : Type*} (S A : ℕ) (parser : Parser α A) (values : List α) (regions : List (Region A)) :
    GeneralPaperFieldDirectoryParsers.Result A :=
  let children := GeneralPaperChildDirectoryCursor.run S A parser values regions
  match children.values,children.remaining with
  | some body,record :: rest =>
    let targets := GeneralPaperNestedArrayFieldCursor.rootWords S A body.roots
    let headers := GeneralPaperFieldDirectory.appendHeaders S A body.headers [⟨record,0,targets.1⟩]
    ⟨some ⟨record,headers.1,body.cells⟩,rest,
      children.work + targets.2 + headers.2 + GeneralPaperLastRegionSelection.price S A record + 128 * (S + A + 1)⟩
  | _,_ => ⟨none,children.remaining,children.work + 64 * (S + A + 1)⟩

theorem on_children {α : Type*} (S A : ℕ) (parser : Parser α A) (values : List α) (regions : List (Region A))
    (body : Body A) (record : Region A) (rest : List (Region A))
    (hChildren : (GeneralPaperChildDirectoryCursor.run S A parser values regions).values = some body)
    (hRemaining : (GeneralPaperChildDirectoryCursor.run S A parser values regions).remaining = record :: rest) :
    (run S A parser values regions).values = some (compose record body) ∧
      (run S A parser values regions).remaining = rest ∧
      (run S A parser values regions).work = (GeneralPaperChildDirectoryCursor.run S A parser values regions).work +
        (GeneralPaperNestedArrayFieldCursor.rootWords S A body.roots).2 +
        (GeneralPaperFieldDirectory.appendHeaders S A body.headers [⟨record,0,body.roots.map Region.reference⟩]).2 +
        GeneralPaperLastRegionSelection.price S A record + 128 * (S + A + 1) := by
  simp only [run,hChildren,hRemaining,GeneralPaperNestedArrayFieldCursor.root_words_data,append_headers_data,compose,and_self]

theorem compose_safe (A : ℕ) (record : Region A) (regions : List (Region A)) (body : Body A)
    (hBody : SafeBody regions body) (hSize : A * body.roots.length ≤ record.length) :
    Safe (regions ++ [record]) (compose record body) := by
  refine ⟨List.mem_append_right _ (List.mem_singleton_self _),?_,?_,?_,hBody.2.2.2.2⟩
  · change ((body.headers ++ [(⟨record,0,body.roots.map Region.reference⟩ : Header A)]).map Header.region).Sublist (regions ++ [record])
    simpa only [List.map_append,List.map_cons,List.map_nil] using hBody.2.1.append (List.Sublist.refl [record])
  · change (body.cells.map GeneralPaperScalarFieldCursor.Cell.region).Sublist (regions ++ [record])
    simpa only [List.append_nil] using hBody.2.2.1.append (List.nil_sublist [record])
  · intro header hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hBody.2.2.2.1 header hh
    · have he := List.mem_singleton.mp hh
      subst header
      change A * (0 + (body.roots.map Region.reference).length) ≤ record.length
      simpa only [List.length_map,Nat.zero_add] using hSize

theorem compose_covered (A : ℕ) (record : Region A) (regions : List (Region A)) (body : Body A)
    (hBody : CoveredBody regions body) : Covered (regions ++ [record]) (compose record body) := by
  unfold Covered compose
  simp only [List.map_append,List.map_cons,List.map_nil]
  have hMove : ((body.headers.map Header.region ++ [record]) ++ body.cells.map GeneralPaperScalarFieldCursor.Cell.region).Perm
      ((body.headers.map Header.region ++ body.cells.map GeneralPaperScalarFieldCursor.Cell.region) ++ [record]) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := [record]) (l₂ := body.cells.map GeneralPaperScalarFieldCursor.Cell.region)).append_left (body.headers.map Header.region)
  exact hMove.trans (hBody.append_right [record])

def expected {α : Type*} (A start arity : ℕ) (schema : α → List ℕ) (child : α → ℕ → Directory A) (values : List α) : Directory A :=
  compose (GeneralPaperTrailingScalarRecord.header A (start + (values.map schema).flatten.sum) arity)
    (GeneralPaperChildDirectorySpecification.collect (GeneralPaperChildDirectorySpecification.directories schema child start values))

theorem success {α : Type*} (model : RationalCostModel) (S A : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (child : α → ℕ → Directory A)
    (hParser : ∀ value start rest,
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).values = some (child value start) ∧
      (parser value ((GeneralPaperSequentialLayout.run model S A start (schema value)).1 ++ rest)).remaining = rest ∧
      Safe (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (child value start))
    (hCovered : ∀ value start,Covered (GeneralPaperSequentialLayout.run model S A start (schema value)).1 (child value start))
    (start arity : ℕ) (values : List α) (rest : List (Region A)) (hArity : values.length ≤ arity) :
    let regions := (GeneralPaperSequentialLayout.run model S A start ((values.map schema).flatten ++ [A * arity])).1
    (run S A parser values (regions ++ rest)).values = some (expected A start arity schema child values) ∧
      (run S A parser values (regions ++ rest)).remaining = rest ∧
      Safe regions (expected A start arity schema child values) ∧ Covered regions (expected A start arity schema child values) := by
  dsimp only
  let first := (GeneralPaperSequentialLayout.run model S A start (values.map schema).flatten).1
  let record := GeneralPaperTrailingScalarRecord.header A (start + (values.map schema).flatten.sum) arity
  let body := GeneralPaperChildDirectorySpecification.collect (GeneralPaperChildDirectorySpecification.directories schema child start values)
  have hRegions : (GeneralPaperSequentialLayout.run model S A start ((values.map schema).flatten ++ [A * arity])).1 = first ++ [record] := by
    rw [GeneralPaperMeasuredLayoutComposition.regions_append,GeneralPaperSequentialLayout.cursor]
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,first,record,GeneralPaperTrailingScalarRecord.header]
  obtain ⟨hv,hr,hs⟩ := GeneralPaperChildDirectorySpecification.success model S A parser schema child hParser start values (record :: rest)
  change (GeneralPaperChildDirectoryCursor.run S A parser values (first ++ record :: rest)).values = some body at hv
  change (GeneralPaperChildDirectoryCursor.run S A parser values (first ++ record :: rest)).remaining = record :: rest at hr
  have hCount := GeneralPaperChildDirectoryCursor.root_count S A parser values _ body hv
  obtain ⟨hRun,hRest,_⟩ := on_children S A parser values _ body record rest hv hr
  rw [hRegions,List.append_assoc,List.singleton_append]
  refine ⟨hRun,hRest,compose_safe A record first body hs ?_,compose_covered A record first body
    (GeneralPaperFieldDirectoryPartition.children model S A schema child hCovered start values)⟩
  change A * body.roots.length ≤ A * arity
  rw [hCount]
  exact Nat.mul_le_mul_left A hArity

end Blotto.GeneralPaperTrailingDirectoryRecord
