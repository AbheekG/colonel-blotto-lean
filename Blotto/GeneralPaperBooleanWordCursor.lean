import Blotto.GeneralPaperFrontDirectoryList

/-! Existing retained Boolean words: source bits, the measured list header,
and one trailing 16-word record. Source mapping is priced; no integer value
is re-encoded and no supplied footprint is evaluated during extraction. -/
namespace Blotto.GeneralPaperBooleanWordCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def bitsRun (S A : ℕ) (values : List Bool) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  let mapped := GeneralPaperScalarRecordComponents.lift S A Scalar.bit values
  let parsed := GeneralPaperScalarRecordComponents.listRun S A 32 mapped.1 regions
  ⟨parsed.values,parsed.remaining,mapped.2 + parsed.work + 64 * (S + A + 1)⟩
def bitsExpected (model : RationalCostModel) (S A start : ℕ) (values : List Bool) : Directory A :=
  GeneralPaperScalarRecordComponents.listExpected model S A start 32 2 (values.map Scalar.bit)
def bitsSchema (model : RationalCostModel) (S A : ℕ) (values : List Bool) : List ℕ :=
  (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.bit S) values).sizes

theorem bits_plan (model : RationalCostModel) (S A : ℕ) (values : List Bool) :
    bitsSchema model S A values = A * (2 * (values.map Scalar.bit).length + 32) :: (values.map Scalar.bit).map encode := by
  rw [bitsSchema,GeneralPaperMeasuredListBlockPlan.data]
  simp only [List.length_map,List.singleton_append]
  congr 1
  induction values with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.flatten_cons]
    exact congrArg (List.cons 1) ih

theorem bits_success (model : RationalCostModel) (S A start : ℕ) (values : List Bool) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (bitsSchema model S A values)).1
    (bitsRun S A values (regions ++ rest)).values = some (bitsExpected model S A start values) ∧
      (bitsRun S A values (regions ++ rest)).remaining = rest ∧
      Safe regions (bitsExpected model S A start values) ∧ Covered regions (bitsExpected model S A start values) := by
  simpa only [bits_plan,bitsRun,bitsExpected,GeneralPaperScalarRecordComponents.lift_data] using
    GeneralPaperScalarRecordComponents.list_success model S A start 32 2 (values.map Scalar.bit) rest (by decide)

def expected {w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedBinaryWord w) (start : ℕ) : Directory A :=
  GeneralPaperTrailingDirectoryRecord.expected A start 16 (fun _ : Unit => bitsSchema model S A source.bits)
    (fun _ start => bitsExpected model S A start source.bits) [()]
def run {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperTrailingDirectoryRecord.run S A (fun _ : Unit => bitsRun S A source.bits) [()] regions

theorem plan {w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedBinaryWord w) :
    (GeneralPaperEqualMeasuredLeafPlans.word model S A source).sizes =
      (([()] : List Unit).map (fun _ => bitsSchema model S A source.bits)).flatten ++ [A * 16] := by
  simp only [GeneralPaperEqualMeasuredLeafPlans.word,GeneralPaperMeasuredBlockPlan.join_data,
    GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,
    bitsSchema,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,Nat.mul_zero,Nat.zero_add]

theorem success {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedBinaryWord w) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.word model S A source)).1
    (run S A source (regions ++ rest)).values = some (expected model S A source start) ∧
      (run S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A source start) ∧ Covered regions (expected model S A source start) := by
  have hp := fun (_ : Unit) start rest => And.intro (bits_success model S A start source.bits rest).1
    (And.intro (bits_success model S A start source.bits rest).2.1 (bits_success model S A start source.bits rest).2.2.1)
  have hc := fun (_ : Unit) start => (bits_success model S A start source.bits []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,run,expected] using
    GeneralPaperTrailingDirectoryRecord.success model S A (fun _ : Unit => bitsRun S A source.bits)
      (fun _ : Unit => bitsSchema model S A source.bits) (fun _ start => bitsExpected model S A start source.bits)
      hp hc start 16 [()] rest (by decide)

end Blotto.GeneralPaperBooleanWordCursor
