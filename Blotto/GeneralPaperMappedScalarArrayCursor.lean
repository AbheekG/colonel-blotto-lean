import Blotto.GeneralPaperScalarArrayFieldCursor

/-! Existing retained rational/natural arrays feed the scalar field parser.
Their measured regions are used unchanged. A priced source traversal injects
values into the typed scalar model once; encoded payload work is summed, not
charged at the largest scalar precision once per coordinate. -/
namespace Blotto.GeneralPaperMappedScalarArrayCursor
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def liftValues {α : Type*} (S A : ℕ) (lift : α → Scalar) : List α → List Scalar × ℕ
  | [] => ([],64 * (S + A + 1))
  | value :: values =>
    let actual := lift value
    let later := liftValues S A lift values
    (actual :: later.1,later.2 + encode actual + 64 * (S + A + 1))

theorem lift_data {α : Type*} (S A : ℕ) (lift : α → Scalar) (values : List α) :
    (liftValues S A lift values).1 = values.map lift := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [liftValues,ih,List.map_cons]

theorem lift_work {α : Type*} (S A : ℕ) (lift : α → Scalar) (values : List α) :
    (liftValues S A lift values).2 = (values.map (fun value => encode (lift value))).sum +
      (values.length + 1) * (64 * (S + A + 1)) := by
  induction values with
  | nil => simp only [liftValues,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
  | cons value values ih => simp only [liftValues,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

def run {α : Type*} {n : ℕ} (S A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (regions : List (Region A)) : GeneralPaperScalarArrayFieldCursor.Result A :=
  let values := liftValues S A lift source.data.toList
  let actual := GeneralPaperScalarArrayFieldCursor.run S A values.1 regions
  ⟨actual.values,actual.remaining,values.2 + actual.work + 64 * (S + A + 1)⟩

theorem run_values {α : Type*} {n : ℕ} (S A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (regions : List (Region A)) :
    (run S A lift source regions).values =
      (GeneralPaperScalarArrayFieldCursor.run S A (source.data.toList.map lift) regions).values := by
  simp only [run,lift_data]

theorem run_remaining {α : Type*} {n : ℕ} (S A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (regions : List (Region A)) :
    (run S A lift source regions).remaining =
      (GeneralPaperScalarArrayFieldCursor.run S A (source.data.toList.map lift) regions).remaining := by
  simp only [run,lift_data]

theorem run_work {α : Type*} {n : ℕ} (S A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (regions : List (Region A)) :
    (run S A lift source regions).work = (source.data.toList.map (fun value => encode (lift value))).sum +
      (n + 1) * (64 * (S + A + 1)) +
      (GeneralPaperScalarArrayFieldCursor.run S A (source.data.toList.map lift) regions).work + 64 * (S + A + 1) := by
  dsimp only [run]
  rw [lift_work,lift_data,Array.length_toList,source.size]

def expected (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) : GeneralPaperScalarArrayFieldCursor.Fields A :=
  GeneralPaperScalarArrayFieldCursor.fields A (GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length)
    (GeneralPaperScalarFieldCursor.cells A
      (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1 values)

theorem rational_plan {n : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n ℚ) :
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source).sizes =
      A * (64 + (source.data.toList.map Scalar.rational).length) :: (source.data.toList.map Scalar.rational).map encode := by
  have h := GeneralPaperScalarArrayLayout.plan_data model S A (GeneralPaperMeasuredBlockPlan.rational model S)
    rationalWordWidth source (GeneralPaperMeasuredBlockPlan.rational_data model S)
  simpa only [GeneralPaperScalarArrayLayout.plan,List.length_map,Array.length_toList,source.size,List.map_map,encode,Function.comp_def,Nat.add_comm] using h

theorem natural_plan {n : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable n ℕ) :
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source).sizes =
      A * (64 + (source.data.toList.map Scalar.natural).length) :: (source.data.toList.map Scalar.natural).map encode := by
  have h := GeneralPaperScalarArrayLayout.plan_data model S A (GeneralPaperMeasuredBlockPlan.natural model S)
    GeneralPaperEncodedScalarStorage.natBits source (GeneralPaperMeasuredBlockPlan.natural_data model S)
  simpa only [GeneralPaperScalarArrayLayout.plan,List.length_map,Array.length_toList,source.size,List.map_map,encode,Function.comp_def,Nat.add_comm] using h

theorem rational_success {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℚ)
    (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source)).1
    let fields := expected model S A start (source.data.toList.map Scalar.rational)
    (run S A Scalar.rational source (regions ++ rest)).values = some fields ∧
      (run S A Scalar.rational source (regions ++ rest)).remaining = rest ∧
      GeneralPaperReferenceRegionSlots.Valid fields.header ∧ ∀ cell ∈ fields.cells,cell.Fits := by
  dsimp only
  rw [run_values,run_remaining]
  simpa only [GeneralPaperMeasuredBlockLayout.run,rational_plan,expected] using
    GeneralPaperScalarArrayFieldCursor.layout_success model S A start (source.data.toList.map Scalar.rational) rest

theorem natural_success {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℕ)
    (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source)).1
    let fields := expected model S A start (source.data.toList.map Scalar.natural)
    (run S A Scalar.natural source (regions ++ rest)).values = some fields ∧
      (run S A Scalar.natural source (regions ++ rest)).remaining = rest ∧
      GeneralPaperReferenceRegionSlots.Valid fields.header ∧ ∀ cell ∈ fields.cells,cell.Fits := by
  dsimp only
  rw [run_values,run_remaining]
  simpa only [GeneralPaperMeasuredBlockLayout.run,natural_plan,expected] using
    GeneralPaperScalarArrayFieldCursor.layout_success model S A start (source.data.toList.map Scalar.natural) rest

end Blotto.GeneralPaperMappedScalarArrayCursor
