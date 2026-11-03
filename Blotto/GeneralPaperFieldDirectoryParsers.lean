import Blotto.GeneralPaperFieldDirectorySafety

/-! Existing scalar-array cursor outputs are lifted to temporary directory
outputs. No scalar is remeasured and no installation runs during this lift.
Nested parsers receive the actual source and remaining region stream. -/
namespace Blotto.GeneralPaperFieldDirectoryParsers
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout
open GeneralPaperFieldDirectorySafety (Safe)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Result (A : ℕ) where
  values : Option (Directory A)
  remaining : List (Region A)
  work : ℕ

abbrev Parser (α : Type*) (A : ℕ) := α → List (Region A) → Result A

def fromArray (S A : ℕ) (parsed : GeneralPaperScalarArrayFieldCursor.Result A) : Result A :=
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some fields =>
    ⟨some (ofArray fields),parsed.remaining,
      parsed.work + GeneralPaperLastRegionSelection.price S A fields.header.region + 64 * (S + A + 1)⟩

def rational {n : ℕ} (S A : ℕ) (source : FixedArrayTable n ℚ) (regions : List (Region A)) : Result A :=
  fromArray S A (GeneralPaperMappedScalarArrayCursor.run S A GeneralPaperRetainedScalarValue.Scalar.rational source regions)

def natural {n : ℕ} (S A : ℕ) (source : FixedArrayTable n ℕ) (regions : List (Region A)) : Result A :=
  fromArray S A (GeneralPaperMappedScalarArrayCursor.run S A GeneralPaperRetainedScalarValue.Scalar.natural source regions)

theorem rational_success {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℚ)
    (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source)).1
    let directory := ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start
      (source.data.toList.map GeneralPaperRetainedScalarValue.Scalar.rational))
    (rational S A source (regions ++ rest)).values = some directory ∧
      (rational S A source (regions ++ rest)).remaining = rest ∧ Safe regions directory := by
  dsimp only
  obtain ⟨hv,hr,_⟩ := GeneralPaperMappedScalarArrayCursor.rational_success model S A start source rest
  refine ⟨?_,?_,GeneralPaperFieldDirectorySafety.scalar_rational model S A start source⟩
  · simp only [rational,fromArray,hv]
  · simp only [rational,fromArray,hv,hr]

theorem natural_success {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℕ)
    (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source)).1
    let directory := ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start
      (source.data.toList.map GeneralPaperRetainedScalarValue.Scalar.natural))
    (natural S A source (regions ++ rest)).values = some directory ∧
      (natural S A source (regions ++ rest)).remaining = rest ∧ Safe regions directory := by
  dsimp only
  obtain ⟨hv,hr,_⟩ := GeneralPaperMappedScalarArrayCursor.natural_success model S A start source rest
  refine ⟨?_,?_,GeneralPaperFieldDirectorySafety.scalar_natural model S A start source⟩
  · simp only [natural,fromArray,hv]
  · simp only [natural,fromArray,hv,hr]

theorem from_array_work (S A : ℕ) (parsed : GeneralPaperScalarArrayFieldCursor.Result A)
    (fields : GeneralPaperScalarArrayFieldCursor.Fields A) (hParsed : parsed.values = some fields) :
    (fromArray S A parsed).work = parsed.work + GeneralPaperLastRegionSelection.price S A fields.header.region +
      64 * (S + A + 1) := by simp only [fromArray,hParsed]

end Blotto.GeneralPaperFieldDirectoryParsers
