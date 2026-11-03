import Blotto.BinaryLifetimeEntriesMeasured
import Blotto.BinaryPRGNumericalEntriesMeasured
import Blotto.BinaryPRGNumericalPhysicalMapMeasured
import Blotto.BinaryPRGPromiseMeasured

/-! One actual measured numerical preparation shares its returned arithmetic
entries between compatibility packs and both physical stores. The accepted
old physical object/readbacks and trace are exact. Measured promise checking
runs first and rejects before numerical allocation. Native model joins remain. -/
namespace Blotto.BinaryPRGCheckedPhysicalPreparationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition BinaryPRGPreparation
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGCheckedPhysicalPreparationLifetime (PreparedPhysical)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def prepare {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : (PreparedPhysical n × Trace) × ℕ :=
  let entries := BinaryPRGNumericalEntriesMeasured.prepare input rows hRows
  let lengths := BinaryLifetimeEntriesMeasured.fromEntries n entries.1.lengths entries.1.lengths_size
  let poor := BinaryLifetimeEntriesMeasured.fromEntries n entries.1.poor entries.1.poor_size
  let physicalLength := BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n entries.1.lengths entries.1.lengths_size
  let physicalPoor := BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n entries.1.poor entries.1.poor_size
  let numericalTrace := wrapList
    (6*n+BinaryPRGNumericalPreparationLifetime.flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input))
    (64+BinaryPRGNumericalPreparationLifetime.flattenArrayReserve n (BinaryPRGPreparationWork.storedInputWidth input))
    (n+4) [entries.1.ratio.2,lengths.1.2,poor.1.2]
  ((⟨⟨input,entries.1.ratio.1,lengths.1.1,poor.1.1⟩,physicalLength.1.1,physicalPoor.1.1,
      (by
        intro index j hIndex
        constructor
        · simpa only [physicalLength,lengths,BinaryLifetimeEntriesMeasured.fromEntries_erases] using
            BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical_readback n entries.1.lengths entries.1.lengths_size index j hIndex
        · simpa only [physicalPoor,poor,BinaryLifetimeEntriesMeasured.fromEntries_erases] using
            BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical_readback n entries.1.poor entries.1.poor_size index j hIndex)⟩,
    wrap 128 2 [numericalTrace,physicalLength.1.2,physicalPoor.1.2]),
    entries.2+lengths.2+poor.2+physicalLength.2+physicalPoor.2+16)

theorem prepare_erases {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : (prepare input rows hRows).1 =
      BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical input rows hRows := by
  simp only [prepare,BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical,
    BinaryPRGNumericalEntriesMeasured.prepare_data,BinaryPRGNumericalEntriesMeasured.reference,
    BinaryLifetimeEntriesMeasured.fromEntries_erases,BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical_erases]

theorem prepare_readback {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace (prepare input rows hRows).1.1.lengthStore index).1 =
        some ((prepare input rows hRows).1.1.numerical.lengths.read j) ∧
      (BinaryWordObjectArrayAccess.getWithTrace (prepare input rows hRows).1.1.poorStore index).1 =
        some ((prepare input rows hRows).1.1.numerical.poorResources.read j) :=
  (prepare input rows hRows).1.1.readback index j hIndex

theorem prepare_charge {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let entries := (BinaryPRGNumericalEntriesMeasured.prepare input rows hRows).1
    (prepare input rows hRows).2 = (BinaryPRGNumericalEntriesMeasured.prepare input rows hRows).2+
      (BinaryLifetimeEntriesMeasured.fromEntries n entries.lengths entries.lengths_size).2+
      (BinaryLifetimeEntriesMeasured.fromEntries n entries.poor entries.poor_size).2+
      (BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n entries.lengths entries.lengths_size).2+
      (BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n entries.poor entries.poor_size).2+16 := rfl

def checked {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (Option {prepared : PreparedPhysical n // prepared.numerical.Valid} × Trace) × ℕ :=
  let tested := BinaryPRGPromiseMeasured.checkRows input rows
  if h : tested.1.1 = true then
    let prepared := prepare input rows hRows
    have hCheck : input.Checks := (checkBool_iff input hC).mp
      ((BinaryPRGPromiseMeasured.checkRows_state input hC rows hRows).symm.trans h)
    have hValid : prepared.1.1.numerical.Valid := by
      rw [prepare_erases,BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical_numerical,
        BinaryPRGNumericalPreparationLifetime.prepareWithRows_state input hC rows hRows]
      exact prepare_valid input hC hCheck
    ((some ⟨prepared.1.1,hValid⟩,wrap 32 2 [tested.1.2,prepared.1.2]),tested.2+prepared.2+8)
  else ((none,wrap 16 2 [tested.1.2]),tested.2+4)

theorem checked_erases {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checked input hC rows hRows).1 =
      BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows input hC rows hRows := by
  unfold checked BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
  dsimp only
  by_cases h : (BinaryPRGPromiseMeasured.checkRows input rows).1.1 = true
  · have ho : (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).1 = true :=
      (congrArg Prod.fst (BinaryPRGPromiseMeasured.checkRows_erases input rows)).symm.trans h
    rw [dite_eq_left h,dite_eq_left ho]
    simp only [prepare_erases,BinaryPRGPromiseMeasured.checkRows_erases]
  · have ho : ¬ (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).1 = true :=
      fun ht => h ((congrArg Prod.fst (BinaryPRGPromiseMeasured.checkRows_erases input rows)).trans ht)
    rw [dite_eq_right h,dite_eq_right ho]
    simp only [BinaryPRGPromiseMeasured.checkRows_erases]

theorem checked_reject {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (h : ¬ (BinaryPRGPromiseMeasured.checkRows input rows).1.1 = true) :
    checked input hC rows hRows = ((none,wrap 16 2 [(BinaryPRGPromiseMeasured.checkRows input rows).1.2]),
      (BinaryPRGPromiseMeasured.checkRows input rows).2+4) := by
  unfold checked
  rw [dite_eq_right h]

theorem checked_work_parts {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checked input hC rows hRows).2 ≤
      (BinaryPRGPromiseMeasured.checkRows input rows).2+(prepare input rows hRows).2+8 := by
  unfold checked
  dsimp only
  split <;> dsimp only <;> omega

end Blotto.BinaryPRGCheckedPhysicalPreparationMeasured
