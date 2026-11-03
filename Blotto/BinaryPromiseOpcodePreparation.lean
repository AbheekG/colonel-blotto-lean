import Blotto.BinaryPromiseCheckPlan
import Blotto.BinaryNumericalOpcodePreparation

/-! The planned promise checker gates actual planned numerical preparation.
Forgetting only promise division/emission recovers the complete preceding
physical record and numerical charge, including zero numerical work on reject. -/
namespace Blotto.BinaryPromiseOpcodePreparation
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition BinaryPRGPreparation
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGCheckedPhysicalPreparationLifetime (PreparedPhysical)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def checked {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (((Option {prepared : PreparedPhysical n // prepared.numerical.Valid} × Trace) × ℕ) × ℕ) × ℕ :=
  let promise := BinaryPromiseCheckPlan.checkRows input rows
  let tested := promise.1
  if h : tested.1.1 = true then
    let extended := BinaryNumericalOpcodePreparation.prepare input rows hRows
    let prepared := extended.1
    have hOld : (BinaryPRGPromiseMeasured.checkRows input rows).1.1 = true :=
      (congrArg (fun out => out.1.1) (BinaryPromiseCheckPlan.checkRows_compat input rows)).symm.trans h
    have hCheck : input.Checks := (checkBool_iff input hC).mp
      ((BinaryPRGPromiseMeasured.checkRows_state input hC rows hRows).symm.trans hOld)
    have hValid : prepared.1.1.numerical.Valid := by
      dsimp only [prepared,extended]
      rw [BinaryNumericalOpcodePreparation.prepare_compat,BinaryPRGCheckedPhysicalPreparationMeasured.prepare_erases,
        BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical_numerical,
        BinaryPRGNumericalPreparationLifetime.prepareWithRows_state input hC rows hRows]
      exact prepare_valid input hC hCheck
    ((((some ⟨prepared.1.1,hValid⟩,wrap 32 2 [tested.1.2,prepared.1.2]),tested.2+prepared.2+8),extended.2),promise.2)
  else ((((none,wrap 16 2 [tested.1.2]),tested.2+4),0),promise.2)

theorem checked_compat {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checked input hC rows hRows).1 = BinaryNumericalOpcodePreparation.checked input hC rows hRows := by
  have hRecord := BinaryPromiseCheckPlan.checkRows_compat input rows
  have hData := congrArg (fun out => out.1.1) hRecord
  unfold checked BinaryNumericalOpcodePreparation.checked
  dsimp only
  simp only [hRecord]
  split <;> rfl

theorem checked_reject_numerical {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (h : ¬ (BinaryPRGPromiseMeasured.checkRows input rows).1.1 = true) :
    (checked input hC rows hRows).1.2 = 0 := by
  have hData := congrArg (fun out => out.1.1) (BinaryPromiseCheckPlan.checkRows_compat input rows)
  have hn : ¬ (BinaryPromiseCheckPlan.checkRows input rows).1.1.1 = true := fun he => h (hData.symm.trans he)
  unfold checked
  rw [dite_eq_right hn]

theorem checked_price {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checked input hC rows hRows).2 ≤ 4*(checked input hC rows hRows).1.1.2+
      25*(checked input hC rows hRows).1.1.1.2.length+5 := by
  have hp := BinaryPromiseCheckPlan.checkRows_price input rows
  unfold checked
  dsimp only
  split <;> dsimp only <;>
    simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under,List.length_map] <;> omega

end Blotto.BinaryPromiseOpcodePreparation
