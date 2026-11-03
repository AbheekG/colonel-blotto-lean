import Blotto.GeneralPaperChildDirectoryLifetime

/-! Concrete rational/natural array parsers discharge the complete child
lifetime predicate at actual measured schemas. The same executed forward
child loop then joins exact body/suffix returns and complete storage.
No callback space or price oracle is supplied to execution. -/
namespace Blotto.GeneralPaperMappedCursorChildLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperFieldDirectoryParsers (Parser)
open GeneralPaperChildDirectoryLifetime (Lifetime)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem mapped_on_layout {α : Type*} {n : ℕ} (model : RationalCostModel) (S A start Q : ℕ) (lift : α → Scalar)
    (source : FixedArrayTable n α) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (A * (64 + (source.data.toList.map lift).length) + ((source.data.toList.map lift).map encode).sum) < 2 ^ A)
    (hWork : (GeneralPaperFieldDirectoryParsers.fromArray S A (GeneralPaperMappedScalarArrayCursor.run S A lift source
      ((GeneralPaperSequentialLayout.run model S A start
        (A * (64 + (source.data.toList.map lift).length) :: (source.data.toList.map lift).map encode)).1 ++ rest))).work ≤ Q) :
    GeneralPaperScalarCursorLifetimeRates.window model S A start lift source rest ≤
      (A * (64 + (source.data.toList.map lift).length) + ((source.data.toList.map lift).map encode).sum + 1) * 48 * unit model S A Q := by
  have hRange := GeneralPaperSequentialLayout.range model S A (start + A * (64 + (source.data.toList.map lift).length))
    ((source.data.toList.map lift).map encode)
  rw [GeneralPaperScalarArrayFieldCursor.layout_regions,List.cons_append] at hWork
  have h := GeneralPaperMappedScalarCursorLifetime.prefix_bound model S A Q lift source _ _ rest hA
    (by rw [GeneralPaperSequentialLayout.count,List.length_map])
    (fun region hr => (hRange region hr).2.trans_lt (by omega))
    (by change start + A * (64 + (source.data.toList.map lift).length) < 2 ^ A; omega) rfl hWork
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 48 (by omega)))

def rationalSchema {n : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n ℚ) : List ℕ :=
  (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source).sizes

def naturalSchema {n : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n ℕ) : List ℕ :=
  (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source).sizes

def rationalExpected {n : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n ℚ) (start : ℕ) : GeneralPaperFieldDirectory.Directory A :=
  GeneralPaperFieldDirectory.ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))

def naturalExpected {n : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n ℕ) (start : ℕ) : GeneralPaperFieldDirectory.Directory A :=
  GeneralPaperFieldDirectory.ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural))

theorem rational_correct {n : ℕ} (model : RationalCostModel) (S A : ℕ) :
    GeneralPaperChildCursorWork.Correct model S A (rationalSchema model S A) (rationalExpected model S A)
      (GeneralPaperFieldDirectoryParsers.rational (n := n) S A) := by
  intro source start rest
  exact GeneralPaperFieldDirectoryParsers.rational_success model S A start source rest

theorem natural_correct {n : ℕ} (model : RationalCostModel) (S A : ℕ) :
    GeneralPaperChildCursorWork.Correct model S A (naturalSchema model S A) (naturalExpected model S A)
      (GeneralPaperFieldDirectoryParsers.natural (n := n) S A) := by
  intro source start rest
  exact GeneralPaperFieldDirectoryParsers.natural_success model S A start source rest

theorem rational_lifetime {n : ℕ} (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    Lifetime model S A 48 (rationalSchema model S A) (GeneralPaperFieldDirectoryParsers.rational (n := n) S A)
      (fun source start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.rational source rest) := by
  intro source start rest Q hCap hWork
  dsimp only [rationalSchema] at hCap ⊢
  rw [GeneralPaperMappedScalarArrayCursor.rational_plan,List.sum_cons] at hCap ⊢
  exact mapped_on_layout model S A start Q Scalar.rational source rest hA hCap (by
    simpa only [rationalSchema,GeneralPaperFieldDirectoryParsers.rational,GeneralPaperMappedScalarArrayCursor.rational_plan] using hWork)

theorem natural_lifetime {n : ℕ} (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    Lifetime model S A 48 (naturalSchema model S A) (GeneralPaperFieldDirectoryParsers.natural (n := n) S A)
      (fun source start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.natural source rest) := by
  intro source start rest Q hCap hWork
  dsimp only [naturalSchema] at hCap ⊢
  rw [GeneralPaperMappedScalarArrayCursor.natural_plan,List.sum_cons] at hCap ⊢
  exact mapped_on_layout model S A start Q Scalar.natural source rest hA hCap (by
    simpa only [naturalSchema,GeneralPaperFieldDirectoryParsers.natural,GeneralPaperMappedScalarArrayCursor.natural_plan] using hWork)

theorem rational_children {n : ℕ} (model : RationalCostModel) (S A start Q : ℕ)
    (values : List (FixedArrayTable n ℚ)) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (values.map (rationalSchema model S A)).flatten.sum < 2 ^ A)
    (hWork : (GeneralPaperChildDirectoryCursor.run S A (GeneralPaperFieldDirectoryParsers.rational S A) values
      ((GeneralPaperSequentialLayout.run model S A start (values.map (rationalSchema model S A)).flatten).1 ++ rest)).work ≤ Q) :
    let output := GeneralPaperChildDirectorySpecification.collect
      (GeneralPaperChildDirectorySpecification.directories (rationalSchema model S A) (rationalExpected model S A) start values)
    let parsed := GeneralPaperChildDirectoryCursor.run S A (GeneralPaperFieldDirectoryParsers.rational S A) values
      ((GeneralPaperSequentialLayout.run model S A start (values.map (rationalSchema model S A)).flatten).1 ++ rest)
    parsed.values = some output ∧ parsed.remaining = rest ∧
      GeneralPaperChildDirectoryLifetime.window model S A (GeneralPaperFieldDirectoryParsers.rational S A)
        (rationalSchema model S A) (rationalExpected model S A)
        (fun source start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.rational source rest) start values rest ≤
      ((values.map (rationalSchema model S A)).flatten.sum + values.length + 1) * 96 * unit model S A Q := by
  dsimp only
  have hCorrect := rational_correct (n := n) model S A
  have hSuccess := GeneralPaperChildDirectorySpecification.success model S A (GeneralPaperFieldDirectoryParsers.rational S A)
    (rationalSchema model S A) (rationalExpected model S A) hCorrect start values rest
  refine ⟨hSuccess.1,hSuccess.2.1,?_⟩
  exact GeneralPaperChildDirectoryLifetime.window_bound model S A 48 Q _ _ _ _ hCorrect (rational_lifetime model S A hA)
    (fun source => GeneralPaperMeasuredPlanPositive.array model S A _ source hA (fun j => GeneralPaperMeasuredPlanPositive.rational model S _))
    hA start values rest hCap hWork

theorem natural_children {n : ℕ} (model : RationalCostModel) (S A start Q : ℕ)
    (values : List (FixedArrayTable n ℕ)) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (values.map (naturalSchema model S A)).flatten.sum < 2 ^ A)
    (hWork : (GeneralPaperChildDirectoryCursor.run S A (GeneralPaperFieldDirectoryParsers.natural S A) values
      ((GeneralPaperSequentialLayout.run model S A start (values.map (naturalSchema model S A)).flatten).1 ++ rest)).work ≤ Q) :
    GeneralPaperChildDirectoryLifetime.window model S A (GeneralPaperFieldDirectoryParsers.natural S A)
      (naturalSchema model S A) (naturalExpected model S A)
      (fun source start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.natural source rest) start values rest ≤
      ((values.map (naturalSchema model S A)).flatten.sum + values.length + 1) * 96 * unit model S A Q := by
  exact GeneralPaperChildDirectoryLifetime.window_bound model S A 48 Q _ _ _ _ (natural_correct model S A) (natural_lifetime model S A hA)
    (fun source => GeneralPaperMeasuredPlanPositive.array model S A _ source hA (fun j => GeneralPaperMeasuredPlanPositive.natural model S _))
    hA start values rest hCap hWork

end Blotto.GeneralPaperMappedCursorChildLifetime
