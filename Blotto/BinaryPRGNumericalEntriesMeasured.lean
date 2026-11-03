import Blotto.BinaryLifetimeMapMeasured
import Blotto.BinaryPRGPromiseControlMeasured
import Blotto.BinaryPRGNumericalPreparationLifetime

/-! Actual quadratic ratio and the two structural arithmetic maps retain
their returned word/trace entries once. Original canonical words derive all
operand widths without a promise-acceptance premise. The reference producer
is used only in erased proofs, not in this measured execution. -/
namespace Blotto.BinaryPRGNumericalEntriesMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition BinaryPRGPreparation
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

structure Entries (n : ℕ) where
  ratio : SignedWord × Trace
  lengths : List (SignedWord × Trace)
  poor : List (SignedWord × Trace)
  lengths_size : lengths.length = n
  poor_size : poor.length = n

def reference {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : Entries n :=
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengths := BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poor := BinaryLifetimeArray.mapDirect (fun item => BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengths
  ⟨ratio,lengths,poor,(by simp [lengths,BinaryLifetimeArray.mapDirect_length,hRows]),
    (by simp [poor,lengths,BinaryLifetimeArray.mapDirect_length,hRows])⟩

def prepare {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : Entries n × ℕ :=
  let ratio := BinaryQuadraticMeasured.apply .div input.b input.a
  let lengths := BinaryLifetimeMapMeasured.map (BinaryQuadraticMeasured.apply .mul two) rows
  let poor := BinaryLifetimeMapMeasured.map (fun item => BinaryQuadraticMeasured.apply .mul ratio.1.1 item.1) lengths.1
  (⟨ratio.1,lengths.1,poor.1,(by rw [BinaryLifetimeMapMeasured.map_length,hRows,List.length_ofFn]),
    (by rw [BinaryLifetimeMapMeasured.map_length,BinaryLifetimeMapMeasured.map_length,hRows,List.length_ofFn])⟩,
    ratio.2+lengths.2+poor.2+8)

theorem prepare_data {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : (prepare input rows hRows).1 = reference input rows hRows := by
  simp only [prepare,reference,BinaryLifetimeMapMeasured.map_data,BinaryQuadraticMeasured.apply_erases]

theorem reference_lengths {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : (reference input rows hRows).lengths =
    List.ofFn (fun j : Fin n => BinaryQuadraticLifetime.applyWithTrace .mul two (input.values.read j)) := by
  simp only [reference,hRows,BinaryLifetimeArray.mapDirect_eq_map,List.map_ofFn,Function.comp_def]

theorem ratio_width {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    width (prepare input rows hRows).1.ratio.1 ≤ 3*BinaryPRGPreparationWork.storedInputWidth input+1 := by
  rw [prepare_data]
  change width (BinaryQuadraticLifetime.applyWithTrace .div input.b input.a).1 ≤ _
  rw [BinaryQuadraticLifetime.applyWithTrace_state .div input.b input.a hC.2.1.1 hC.1.1]
  exact BinaryPRGPreparationWork.ratio_width input

theorem length_width {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (entry : SignedWord × Trace) (he : entry ∈ (prepare input rows hRows).1.lengths) :
    width entry.1 ≤ 3*BinaryPRGPreparationWork.storedInputWidth input+1 := by
  rw [prepare_data,reference_lengths] at he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
  rw [BinaryQuadraticLifetime.applyWithTrace_state .mul two (input.values.read j) two_canonical.1 (hC.2.2 j).1]
  simpa only [BinaryPRGPreparation.prepare,FixedArrayTable.read_ofFn] using
    BinaryPRGPreparationWork.lengths_width input j

def price (n S : ℕ) : ℕ := (2*n+1)*BinaryPRGPromiseControlMeasured.opcodePrice (3*S+1)+8*n+16

theorem price_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) : price n S ≤ price m T := by
  unfold price BinaryPRGPromiseControlMeasured.opcodePrice
  gcongr

theorem prepare_work {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (prepare input rows hRows).2 ≤ price n (BinaryPRGPreparationWork.storedInputWidth input) := by
  let S := BinaryPRGPreparationWork.storedInputWidth input
  let W := 3*S+1
  let ratio := BinaryQuadraticMeasured.apply .div input.b input.a
  let lengths := BinaryLifetimeMapMeasured.map (BinaryQuadraticMeasured.apply .mul two) rows
  let poor := BinaryLifetimeMapMeasured.map (fun item => BinaryQuadraticMeasured.apply .mul ratio.1.1 item.1) lengths.1
  have hOriginal := BinaryPRGPreparationWork.original_widths input
  have hA : width input.a ≤ W := by dsimp [W]; omega
  have hB : width input.b ≤ W := by dsimp [W]; omega
  have hTwo : width two ≤ W := by change 2 ≤ W; dsimp [W]; omega
  have hR := BinaryPRGPromiseControlMeasured.opcode_bound .div input.b input.a W hB hA
  have hL := BinaryLifetimeMapMeasured.map_bound (BinaryQuadraticMeasured.apply .mul two) rows
    (BinaryPRGPromiseControlMeasured.opcodePrice W) (by
      intro word hw
      rw [hRows] at hw
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
      exact BinaryPRGPromiseControlMeasured.opcode_bound .mul two _ W hTwo (by dsimp [W]; have h := hOriginal.2.2.1 j; omega))
  have hRatio : width ratio.1.1 ≤ W := ratio_width input hC rows hRows
  have hLength : ∀ entry ∈ lengths.1,width entry.1 ≤ W := by
    intro entry he
    exact length_width input hC rows hRows entry he
  have hP := BinaryLifetimeMapMeasured.map_bound (fun item => BinaryQuadraticMeasured.apply .mul ratio.1.1 item.1) lengths.1
    (BinaryPRGPromiseControlMeasured.opcodePrice W) (by
      intro entry he
      exact BinaryPRGPromiseControlMeasured.opcode_bound .mul ratio.1.1 entry.1 W hRatio (hLength entry he))
  have hRowsLength : rows.length = n := by rw [hRows,List.length_ofFn]
  have hLengthsLength : lengths.1.length = n := by rw [BinaryLifetimeMapMeasured.map_length,hRowsLength]
  rw [hRowsLength] at hL
  rw [hLengthsLength] at hP
  change ratio.2 ≤ _ at hR
  change lengths.2 ≤ _ at hL
  change poor.2 ≤ _ at hP
  change ratio.2+lengths.2+poor.2+8 ≤ _
  change _ ≤ (2*n+1)*BinaryPRGPromiseControlMeasured.opcodePrice W+8*n+16
  nlinarith

end Blotto.BinaryPRGNumericalEntriesMeasured
