import Blotto.GeneralPaperMappedScalarCursorLifetime

/-! Uniform scalar-cursor storage rates, concrete rational/natural
measured-array instantiations and same-return success/suffix/space joins.
All scalar precision is summed; saved-price widths follow from already
proved executed work. Enclosing record/caller windows remain separate. -/
namespace Blotto.GeneralPaperScalarCursorLifetimeRates
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

theorem generic_profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (workFactor spaceFactor : ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => (B x + 1) * spaceFactor * GeneralPaperMeasuredPlanLifetimeAlgebra.unit model (S x) (A x)
      ((B x + 1) * workFactor * GeneralPaperMeasuredPlanWorkAlgebra.unit model (S x) (A x))) r L := by
  have hOldUnit := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hWork : Bound (fun x => (B x + 1) * workFactor * GeneralPaperMeasuredPlanWorkAlgebra.unit model (S x) (A x)) r L := by fun_prop
  have hQ := bound_small hL hWork hrSmall
  have hUnit := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast S A _ L hL hS hA hQ
  have hMass : Bound (fun x => (B x + 1) * spaceFactor) r L := by fun_prop
  exact bound_mul_polylog _ _ r L hMass hUnit

theorem scalar_profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperScalarFieldCursorLifetime.profile model (S x) (A x) (B x)) r L :=
  generic_profile_rate model hFast S A B r L 4 8 hL hr hS hA hB hrSmall

theorem mapping_profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperScalarSourceMappingLifetime.profile model (S x) (A x) (B x)) r L := by
  simpa only [GeneralPaperScalarSourceMappingLifetime.profile,Nat.mul_one] using
    generic_profile_rate model hFast S A B r L 1 8 hL hr hS hA hB hrSmall

theorem array_profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperScalarArrayCursorLifetime.profile model (S x) (A x) (B x)) r L :=
  generic_profile_rate model hFast S A B r L 8 24 hL hr hS hA hB hrSmall

theorem mapped_profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperMappedScalarCursorLifetime.profile model (S x) (A x) (B x)) r L :=
  generic_profile_rate model hFast S A B r L 16 48 hL hr hS hA hB hrSmall

def window {α : Type*} {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (lift : α → Scalar)
    (source : FixedArrayTable n α) (rest : List (Region A)) : ℕ :=
  let values := source.data.toList.map lift
  GeneralPaperMappedScalarCursorLifetime.window S A lift source
    (GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length)
    (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1 rest

theorem rational_bound {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℚ)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source).sizes.sum < 2 ^ A) :
    window model S A start Scalar.rational source rest ≤ GeneralPaperMappedScalarCursorLifetime.profile model S A
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source).sizes.sum := by
  rw [GeneralPaperMappedScalarArrayCursor.rational_plan,List.sum_cons] at hCap ⊢
  exact GeneralPaperMappedScalarCursorLifetime.layout_bound model S A start Scalar.rational source rest hA hCap

theorem natural_bound {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℕ)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source).sizes.sum < 2 ^ A) :
    window model S A start Scalar.natural source rest ≤ GeneralPaperMappedScalarCursorLifetime.profile model S A
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source).sizes.sum := by
  rw [GeneralPaperMappedScalarArrayCursor.natural_plan,List.sum_cons] at hCap ⊢
  exact GeneralPaperMappedScalarCursorLifetime.layout_bound model S A start Scalar.natural source rest hA hCap

theorem constructed {α : Type*} {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (lift : α → Scalar)
    (source : FixedArrayTable n α) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (A * (64 + (source.data.toList.map lift).length) + ((source.data.toList.map lift).map encode).sum) < 2 ^ A) :
    let values := source.data.toList.map lift
    let regions := (GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: values.map encode)).1 ++ rest
    let returned := GeneralPaperFieldDirectory.ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start values)
    let parsed := GeneralPaperFieldDirectoryParsers.fromArray S A (GeneralPaperMappedScalarArrayCursor.run S A lift source regions)
    parsed.values = some returned ∧ parsed.remaining = rest ∧ window model S A start lift source rest ≤
      GeneralPaperMappedScalarCursorLifetime.profile model S A (A * (64 + values.length) + (values.map encode).sum) := by
  dsimp only
  have hSuccess := GeneralPaperScalarArrayFieldCursor.layout_success model S A start (source.data.toList.map lift) rest
  have hMapped := GeneralPaperMappedScalarArrayCursor.run_values S A lift source
    ((GeneralPaperSequentialLayout.run model S A start
      (A * (64 + (source.data.toList.map lift).length) :: (source.data.toList.map lift).map encode)).1 ++ rest)
  rw [hSuccess.1] at hMapped
  have hRemaining := GeneralPaperMappedScalarArrayCursor.run_remaining S A lift source
    ((GeneralPaperSequentialLayout.run model S A start
      (A * (64 + (source.data.toList.map lift).length) :: (source.data.toList.map lift).map encode)).1 ++ rest)
  rw [hSuccess.2.1] at hRemaining
  refine ⟨?_,?_,GeneralPaperMappedScalarCursorLifetime.layout_bound model S A start lift source rest hA hCap⟩
  · simp only [GeneralPaperFieldDirectoryParsers.fromArray,hMapped,GeneralPaperMappedScalarArrayCursor.expected]
  · simp only [GeneralPaperFieldDirectoryParsers.fromArray,hMapped,hRemaining]

end Blotto.GeneralPaperScalarCursorLifetimeRates
