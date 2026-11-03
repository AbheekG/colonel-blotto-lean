import Blotto.GeneralPaperMappedCursorChildLifetime

/-! Safe measured directory copying and concrete scalar-array child loops
derive complete storage bounds from their executed work. Uniform rates use
measured area plus actual child count, with additive scalar precision.
Outer front/trailing record and full native caller joins remain separate. -/
namespace Blotto.GeneralPaperDirectoryCopyLifetimeRates
open GeneralPaperFieldDirectory (Directory Body)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperSequentialLayout (Region)
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperChildCursorWork (Correct Price)
open GeneralPaperChildDirectoryLifetime (Lifetime)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def prependProfile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (B + 1) * 40 * unit model S A ((B + 1) * 16 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem prepend_actual (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A) (tail : Body A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    GeneralPaperDirectoryPrependLifetime.window S A directory tail ≤
      GeneralPaperDirectoryPrependLifetime.bodyFoot S tail + prependProfile model S A plan.sizes.sum :=
  GeneralPaperDirectoryPrependLifetime.caller_bound model S A start _ plan directory tail hSafe hPos hA hCap
    (GeneralPaperDirectoryCopyWork.prepend_work model S A start plan directory tail hSafe hPos hA hCap)

theorem prepend_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => prependProfile model (S x) (A x) (B x)) r L :=
  GeneralPaperScalarCursorLifetimeRates.generic_profile_rate model hFast S A B r L 16 40 hL hr hS hA hB hrSmall

def childrenProfile (model : RationalCostModel) (S A Cw Cs B N : ℕ) : ℕ :=
  (B + N + 1) * (Cs + 48) * unit model S A ((B + N + 1) * (Cw + 17) * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem children_actual {α : Type*} (model : RationalCostModel) (S A Cw Cs : ℕ) (parser : Parser α A)
    (schema : α → List ℕ) (expected : α → ℕ → Directory A) (space : α → ℕ → List (Region A) → ℕ)
    (hCorrect : Correct model S A schema expected parser) (hLife : Lifetime model S A Cs schema parser space)
    (hPrice : Price model S A Cw schema parser) (hPos : ∀ value,∀ size ∈ schema value,0 < size) (hA : 0 < A)
    (start : ℕ) (values : List α) (rest : List (Region A)) (hCap : start + (values.map schema).flatten.sum < 2 ^ A) :
    GeneralPaperChildDirectoryLifetime.window model S A parser schema expected space start values rest ≤
      childrenProfile model S A Cw Cs (values.map schema).flatten.sum values.length :=
  GeneralPaperChildDirectoryLifetime.window_bound model S A Cs _ parser schema expected space hCorrect hLife hPos hA start values rest hCap
    (GeneralPaperChildCursorWork.children_work model S A Cw parser schema expected hCorrect hPrice hPos hA start values rest hCap)

theorem children_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B N r L : α → ℕ) (Cw Cs : ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hN : Bound N r L) (hrSmall : Small r L) :
    Bound (fun x => childrenProfile model (S x) (A x) Cw Cs (B x) (N x)) r L := by
  have hMass : Bound (fun x => B x + N x) r L := bound_add _ _ r L hL hB hN
  exact GeneralPaperScalarCursorLifetimeRates.generic_profile_rate model hFast S A (fun x => B x + N x) r L
    (Cw + 17) (Cs + 48) hL hr hS hA hMass hrSmall

theorem rational_children {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (values : List (FixedArrayTable n ℚ))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (values.map (GeneralPaperMappedCursorChildLifetime.rationalSchema model S A)).flatten.sum < 2 ^ A) :
    GeneralPaperChildDirectoryLifetime.window model S A (GeneralPaperFieldDirectoryParsers.rational S A)
      (GeneralPaperMappedCursorChildLifetime.rationalSchema model S A) (GeneralPaperMappedCursorChildLifetime.rationalExpected model S A)
      (fun source start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start GeneralPaperRetainedScalarValue.Scalar.rational source rest)
      start values rest ≤ childrenProfile model S A 16 48
        (values.map (GeneralPaperMappedCursorChildLifetime.rationalSchema model S A)).flatten.sum values.length := by
  exact children_actual model S A 16 48 _ _ _ _ (GeneralPaperMappedCursorChildLifetime.rational_correct model S A)
    (GeneralPaperMappedCursorChildLifetime.rational_lifetime model S A hA)
    (fun source start rest hCap => GeneralPaperMappedCursorWork.rational model S A start source rest hA hCap)
    (fun source => GeneralPaperMeasuredPlanPositive.array model S A _ source hA (fun j => GeneralPaperMeasuredPlanPositive.rational model S _))
    hA start values rest hCap

theorem natural_children {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (values : List (FixedArrayTable n ℕ))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (values.map (GeneralPaperMappedCursorChildLifetime.naturalSchema model S A)).flatten.sum < 2 ^ A) :
    GeneralPaperChildDirectoryLifetime.window model S A (GeneralPaperFieldDirectoryParsers.natural S A)
      (GeneralPaperMappedCursorChildLifetime.naturalSchema model S A) (GeneralPaperMappedCursorChildLifetime.naturalExpected model S A)
      (fun source start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start GeneralPaperRetainedScalarValue.Scalar.natural source rest)
      start values rest ≤ childrenProfile model S A 16 48
        (values.map (GeneralPaperMappedCursorChildLifetime.naturalSchema model S A)).flatten.sum values.length := by
  exact children_actual model S A 16 48 _ _ _ _ (GeneralPaperMappedCursorChildLifetime.natural_correct model S A)
    (GeneralPaperMappedCursorChildLifetime.natural_lifetime model S A hA)
    (fun source start rest hCap => GeneralPaperMappedCursorWork.natural model S A start source rest hA hCap)
    (fun source => GeneralPaperMeasuredPlanPositive.array model S A _ source hA (fun j => GeneralPaperMeasuredPlanPositive.natural model S _))
    hA start values rest hCap

end Blotto.GeneralPaperDirectoryCopyLifetimeRates
