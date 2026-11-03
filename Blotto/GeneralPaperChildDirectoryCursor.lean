import Blotto.GeneralPaperFieldDirectoryParsers

/-! Execute each child field parser once, advancing its actual region suffix.
Priced directory concatenation keeps source order and carries explicit work.
The concrete matrix parser fixes the callback to the checked rational-array
parser; no size, decoded-field or cost oracle is an execution input. -/
namespace Blotto.GeneralPaperChildDirectoryCursor
open GeneralPaperFieldDirectory GeneralPaperFieldDirectoryParsers GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Result (A : ℕ) where
  values : Option (Body A)
  remaining : List (Region A)
  work : ℕ

def run {α : Type*} (S A : ℕ) (parser : Parser α A) : List α → List (Region A) → Result A
  | [],regions => ⟨some ⟨[],[],[]⟩,regions,64 * (S + A + 1)⟩
  | value :: values,regions =>
    let child := parser value regions
    match child.values with
    | none => ⟨none,child.remaining,child.work + 64 * (S + A + 1)⟩
    | some directory =>
      let later := run S A parser values child.remaining
      match later.values with
      | none => ⟨none,later.remaining,child.work + later.work + 64 * (S + A + 1)⟩
      | some tail =>
        let actual := GeneralPaperFieldDirectory.prepend S A directory tail
        ⟨some actual.1,later.remaining,child.work + later.work + actual.2 + 64 * (S + A + 1)⟩

theorem step {α : Type*} (S A : ℕ) (parser : Parser α A) (value : α) (values : List α)
    (regions : List (Region A)) (directory : Directory A) (tail : Body A)
    (hChild : (parser value regions).values = some directory)
    (hTail : (run S A parser values (parser value regions).remaining).values = some tail) :
    (run S A parser (value :: values) regions).values = some (GeneralPaperFieldDirectory.prepend S A directory tail).1 ∧
      (run S A parser (value :: values) regions).remaining = (run S A parser values (parser value regions).remaining).remaining ∧
      (run S A parser (value :: values) regions).work = (parser value regions).work +
        (run S A parser values (parser value regions).remaining).work +
        (GeneralPaperFieldDirectory.prepend S A directory tail).2 + 64 * (S + A + 1) := by
  simp only [run,hChild,hTail,and_self]

theorem root_count {α : Type*} (S A : ℕ) (parser : Parser α A) (values : List α) (regions : List (Region A))
    (body : Body A) (hResult : (run S A parser values regions).values = some body) :
    body.roots.length = values.length := by
  induction values generalizing regions body with
  | nil =>
    change some (⟨[],[],[]⟩ : Body A) = some body at hResult
    have hEq := Option.some.inj hResult
    rw [← hEq]
    rfl
  | cons value values ih =>
    cases hChild : (parser value regions).values with
    | none => simp only [run,hChild] at hResult; cases hResult
    | some directory =>
      cases hTail : (run S A parser values (parser value regions).remaining).values with
      | none => simp only [run,hChild,hTail] at hResult; cases hResult
      | some tail =>
        simp only [run,hChild,hTail,Option.some.injEq] at hResult
        rw [← hResult,prepend_roots,List.length_cons,List.length_cons,ih _ tail hTail]

end Blotto.GeneralPaperChildDirectoryCursor
