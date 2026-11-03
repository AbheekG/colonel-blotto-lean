import Blotto.BinaryNumericalOpcodeEntries
import Blotto.BinaryPRGCheckedPhysicalPreparationMeasured

/-! Planned numerical opcodes feed the actual compatibility tables and both
physical stores. Promise checks still reject before numerical allocation.
Full old physical preparation records remain exact; extra opcode work is
forwarded without replaying numerical preparation or its arithmetic passes. -/
namespace Blotto.BinaryNumericalOpcodePreparation
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition BinaryPRGPreparation
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGCheckedPhysicalPreparationLifetime (PreparedPhysical)
open BinaryNumericalOpcodeEntries (entryPayload)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem entryPayload_fromEntries {α : Type*} (n : ℕ) (entries : List (α × Trace)) (hEntries : entries.length = n) :
    entryPayload entries ≤ (BinaryLifetimeEntriesMeasured.fromEntries n entries hEntries).1.2.length := by
  rw [BinaryLifetimeEntriesMeasured.fromEntries_erases]
  simp only [entryPayload,BinaryLifetimeArray.fromEntries,List.length_append,
    List.length_cons,List.length_nil,under,List.length_map,BinaryLifetimeFlattenList.flattenDirect_result]
  omega

def prepare {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : ((PreparedPhysical n × Trace) × ℕ) × ℕ :=
  let extended := BinaryNumericalOpcodeEntries.prepare input rows hRows
  let entries := extended.1
  let lengths := BinaryLifetimeEntriesMeasured.fromEntries n entries.1.lengths entries.1.lengths_size
  let poor := BinaryLifetimeEntriesMeasured.fromEntries n entries.1.poor entries.1.poor_size
  let physicalLength := BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n entries.1.lengths entries.1.lengths_size
  let physicalPoor := BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n entries.1.poor entries.1.poor_size
  let numericalTrace := wrapList
    (6*n+BinaryPRGNumericalPreparationLifetime.flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input))
    (64+BinaryPRGNumericalPreparationLifetime.flattenArrayReserve n (BinaryPRGPreparationWork.storedInputWidth input))
    (n+4) [entries.1.ratio.2,lengths.1.2,poor.1.2]
  (((⟨⟨input,entries.1.ratio.1,lengths.1.1,poor.1.1⟩,physicalLength.1.1,physicalPoor.1.1,
      (by
        intro index j hIndex
        constructor
        · simpa only [physicalLength,lengths,BinaryLifetimeEntriesMeasured.fromEntries_erases] using
            BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical_readback n entries.1.lengths entries.1.lengths_size index j hIndex
        · simpa only [physicalPoor,poor,BinaryLifetimeEntriesMeasured.fromEntries_erases] using
            BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical_readback n entries.1.poor entries.1.poor_size index j hIndex)⟩,
    wrap 128 2 [numericalTrace,physicalLength.1.2,physicalPoor.1.2]),
    entries.2+lengths.2+poor.2+physicalLength.2+physicalPoor.2+16),extended.2)

theorem prepare_compat {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    (prepare input rows hRows).1 = BinaryPRGCheckedPhysicalPreparationMeasured.prepare input rows hRows := by
  simp only [prepare,BinaryPRGCheckedPhysicalPreparationMeasured.prepare,BinaryNumericalOpcodeEntries.prepare_compat]

attribute [local irreducible] BinaryNumericalOpcodeEntries.prepare
  BinaryLifetimeEntriesMeasured.fromEntries BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical

theorem prepare_price {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    (prepare input rows hRows).2 ≤ 4*(prepare input rows hRows).1.2+
      25*(prepare input rows hRows).1.1.2.length+5 := by
  let entries := (BinaryNumericalOpcodeEntries.prepare input rows hRows).1.1
  have hp := BinaryNumericalOpcodeEntries.prepare_price input rows hRows
  have hl := entryPayload_fromEntries n entries.lengths entries.lengths_size
  have hr := entryPayload_fromEntries n entries.poor entries.poor_size
  change (BinaryNumericalOpcodeEntries.prepare input rows hRows).2 ≤
    4*(BinaryNumericalOpcodeEntries.prepare input rows hRows).1.2+
      25*(entries.ratio.2.length+entryPayload entries.lengths+entryPayload entries.poor)+5 at hp
  unfold prepare
  dsimp only
  simp only [wrapList,wrap,combine,List.length_append,List.length_cons,List.length_nil,under,List.length_map]
  dsimp only [entries] at hp hl hr
  omega

def checked {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    ((Option {prepared : PreparedPhysical n // prepared.numerical.Valid} × Trace) × ℕ) × ℕ :=
  let tested := BinaryPRGPromiseMeasured.checkRows input rows
  if h : tested.1.1 = true then
    let extended := prepare input rows hRows
    let prepared := extended.1
    have hCheck : input.Checks := (checkBool_iff input hC).mp
      ((BinaryPRGPromiseMeasured.checkRows_state input hC rows hRows).symm.trans h)
    have hValid : prepared.1.1.numerical.Valid := by
      dsimp only [prepared,extended]
      rw [prepare_compat,BinaryPRGCheckedPhysicalPreparationMeasured.prepare_erases,
        BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical_numerical,
        BinaryPRGNumericalPreparationLifetime.prepareWithRows_state input hC rows hRows]
      exact prepare_valid input hC hCheck
    (((some ⟨prepared.1.1,hValid⟩,wrap 32 2 [tested.1.2,prepared.1.2]),tested.2+prepared.2+8),extended.2)
  else (((none,wrap 16 2 [tested.1.2]),tested.2+4),0)

theorem checked_compat {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checked input hC rows hRows).1 = BinaryPRGCheckedPhysicalPreparationMeasured.checked input hC rows hRows := by
  unfold checked BinaryPRGCheckedPhysicalPreparationMeasured.checked
  dsimp only
  by_cases h : (BinaryPRGPromiseMeasured.checkRows input rows).1.1 = true
  · rw [dite_eq_left h,dite_eq_left h]
    simp only [prepare_compat]
  · rw [dite_eq_right h,dite_eq_right h]

theorem checked_reject {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (h : ¬ (BinaryPRGPromiseMeasured.checkRows input rows).1.1 = true) :
    (checked input hC rows hRows).2 = 0 := by
  unfold checked
  rw [dite_eq_right h]

theorem checked_price {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checked input hC rows hRows).2 ≤ 4*(checked input hC rows hRows).1.2+
      25*(checked input hC rows hRows).1.1.2.length+5 := by
  have hp := prepare_price input rows hRows
  unfold checked
  dsimp only
  split <;> dsimp only <;>
    simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under,List.length_map] <;> omega

end Blotto.BinaryNumericalOpcodePreparation
