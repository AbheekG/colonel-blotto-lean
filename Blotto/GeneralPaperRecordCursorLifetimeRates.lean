import Blotto.GeneralPaperTrailingRecordCursorLifetime

/-! Existing executed-work bounds discharge the saved-price condition for
front lists, nested arrays and trailing records. Generic child contracts
are erased proof hypotheses; no callback cost is supplied to execution. -/
namespace Blotto.GeneralPaperRecordCursorLifetimeRates
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperSequentialLayout (Region)
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperChildCursorWork (Correct Price)
open GeneralPaperChildDirectoryLifetime (Lifetime)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def profile (model : RationalCostModel) (S A B Cw Cs : ℕ) : ℕ :=
  (B + 1) * Cs * unit model S A ((B + 1) * Cw * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem raise {α : Type*} (model : RationalCostModel) (S A C D : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (space : α → ℕ → List (Region A) → ℕ)
    (hLife : Lifetime model S A C schema parser space) (hCD : C ≤ D) :
    Lifetime model S A D schema parser space := by
  intro value start rest Q hCap hWork
  exact (hLife value start rest Q hCap hWork).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (List.sum (schema value) + 1) hCD))

theorem array_actual {α : Type*} (model : RationalCostModel) (S A Cw Cs : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A Cs schema parser space)
    (hPrice : Price model S A Cw schema parser) (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (A * (64 + values.length) + (values.map schema).flatten.sum) < 2 ^ A) :
    GeneralPaperFrontRecordCursorLifetime.window model S A 64 1 parser schema expected space start values rest ≤
      profile model S A (A * (64 + values.length) + (values.map schema).flatten.sum) (Cw + 24) (Cs + 64) :=
  GeneralPaperFrontRecordCursorLifetime.array_bound model S A Cs _ parser schema expected space hCorrect hLife hPos hA start values rest hCap
    (GeneralPaperRecordCursorWork.nested model S A Cw parser schema expected hCorrect hPrice hPos hA start values rest hCap)

theorem list_actual {α : Type*} (model : RationalCostModel) (S A Cw Cs : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A Cs schema parser space)
    (hPrice : Price model S A Cw schema parser) (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A))
    (hCap : start + (A * (2 * values.length + 32) + (values.map schema).flatten.sum) < 2 ^ A) :
    GeneralPaperFrontRecordCursorLifetime.window model S A 32 2 parser schema expected space start values rest ≤
      profile model S A (A * (2 * values.length + 32) + (values.map schema).flatten.sum) (Cw + 24) (Cs + 64) :=
  GeneralPaperFrontRecordCursorLifetime.list_bound model S A Cs _ parser schema expected space hCorrect hLife hPos hA start values rest hCap
    (GeneralPaperFrontCursorWork.front model S A Cw parser schema expected hCorrect hPrice hPos hA start values rest hCap)

theorem trailing_actual {α : Type*} (model : RationalCostModel) (S A Cw Cs : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A Cs schema parser space)
    (hPrice : Price model S A Cw schema parser) (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start arity : ℕ) (values : List α) (rest : List (Region A)) (hArity : values.length ≤ arity)
    (hCap : start + ((values.map schema).flatten.sum + A * arity) < 2 ^ A) :
    GeneralPaperTrailingRecordCursorLifetime.window model S A start arity parser schema expected space values rest ≤
      profile model S A ((values.map schema).flatten.sum + A * arity) (Cw + 32) (Cs + 96) :=
  GeneralPaperTrailingRecordCursorLifetime.window_bound model S A Cs _ parser schema expected space hCorrect hLife hPos hA start arity values rest hArity hCap
    (GeneralPaperRecordCursorWork.trailing model S A Cw parser schema expected hCorrect hPrice hPos hA start arity values rest hArity hCap)

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (Cw Cs : ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => profile model (S x) (A x) (B x) Cw Cs) r L :=
  GeneralPaperScalarCursorLifetimeRates.generic_profile_rate model hFast S A B r L Cw Cs hL hr hS hA hB hrSmall

end Blotto.GeneralPaperRecordCursorLifetimeRates
