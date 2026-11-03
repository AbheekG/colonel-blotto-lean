import Blotto.PRGPhysicalArrayInterface
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! One complete physical array preparation/lookup executes the actual
returned heap and slot tape once. Both work phases and all retained versions
join, with closed original-frame polynomial bounds at the PRG interfaces.
The incoming decoded word list is borrowed; forming it from a native source
array and universal full-sampler adoption are not charged away here. -/
namespace Blotto.PRGPhysicalArrayRun
open BinaryRationalNormalization BinaryWordObjectArray BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open PRGPhysicalArrayInterface
set_option maxHeartbeats 3000000

def runWithWork (words : List SignedWord) (index : List Bool) : Option SignedWord × ℕ :=
  let prepared := BinaryWordObjectArrayLifetime.prepareWithWork words
  let result := getWithWork prepared.1 index
  (result.1,prepared.2+result.2+8)

def runWithTrace (words : List SignedWord) (index : List Bool) : Option SignedWord × Trace :=
  let prepared := BinaryWordObjectArrayLifetime.prepareWithTrace words
  let result := BinaryWordObjectArrayAccess.getWithTrace prepared.1 index
  (result.1,wrap 64 2 [prepared.2,result.2])

theorem runWithWork_state (words : List SignedWord) (index : List Bool) :
    (runWithWork words index).1 = words[BinaryBigEndian.littleValue index]? := by
  simp only [runWithWork,getWithWork_state,BinaryWordObjectArrayLifetime.prepareWithWork_state,get_prepare]

theorem run_state (words : List SignedWord) (index : List Bool) :
    (runWithTrace words index).1 = (runWithWork words index).1 := by
  simp only [runWithTrace,runWithWork,BinaryWordObjectArrayAccess.get_state,
    BinaryWordObjectArrayLifetime.prepareWithTrace_state,BinaryWordObjectArrayLifetime.prepareWithWork_state]

theorem raw_work_bound (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request)
    (index : List Bool) (hIndex : index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1) :
    (runWithWork table.data.toList index).2 ≤ preparationBound frame.length+readWorkBound frame.length+8 := by
  have hp := raw_preparation_work_bound frame parsed hRead table hTable
  have hr := (raw_read_bounds frame parsed hRead table hTable index hIndex).1
  have hStores : (BinaryWordObjectArrayLifetime.prepareWithWork table.data.toList).1 = (prepareTable table).1 := by
    rw [BinaryWordObjectArrayLifetime.prepareWithWork_state,prepareTable,BinaryWordObjectArrayLifetime.prepareWithTrace_state]
  change _+_+8 ≤ _
  rw [hStores]
  omega

theorem raw_usage (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request)
    (index : List Bool) (hIndex : index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1) :
    usage (runWithTrace table.data.toList index).2 ≤ preparationBound frame.length+PRGPhysicalArrayInterface.readEnvelope frame.length+128 := by
  have hp := raw_preparation_bound frame parsed hRead table hTable
  change usage (BinaryWordObjectArrayLifetime.prepareWithTrace table.data.toList).2 ≤ _ at hp
  have hr := (raw_read_bounds frame parsed hRead table hTable index hIndex).2
  have hw := wrap_usage 64 2 [(BinaryWordObjectArrayLifetime.prepareWithTrace table.data.toList).2,
    (BinaryWordObjectArrayAccess.getWithTrace (prepareTable table).1 index).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace table.data.toList index).2 ≤ _ at hw
  omega

theorem raw_all_prefix (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request)
    (index : List Bool) (hIndex : index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace table.data.toList index).2 steps ≤ borrowed+preparationBound frame.length+PRGPhysicalArrayInterface.readEnvelope frame.length+128 ∧
      framePeak ((runWithTrace table.data.toList index).2.take steps) ≤ preparationBound frame.length+PRGPhysicalArrayInterface.readEnvelope frame.length+128 := by
  simpa only [Nat.add_assoc] using BinaryPRGHeapTraceUsage.all_prefix _ _
    (raw_usage frame parsed hRead table hTable index hIndex) borrowed steps

theorem raw_native_lookup (frame : List Bool) (parsed : PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (table : FixedArrayTable parsed.1.1 SignedWord) (hTable : table ∈ tables parsed.1.2.request) (j : Fin parsed.1.1) :
    ∃ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace table.data.toList).1,
      (runWithTrace table.data.toList index).1 = some (table.read j) ∧
      (runWithWork table.data.toList index).2 ≤ preparationBound frame.length+readWorkBound frame.length+8 ∧
      usage (runWithTrace table.data.toList index).2 ≤ preparationBound frame.length+PRGPhysicalArrayInterface.readEnvelope frame.length+128 := by
  obtain ⟨index,hIndex,hValue⟩ := word_for_index table j
  refine ⟨index,hIndex,?_,raw_work_bound frame parsed hRead table hTable index hIndex,
    raw_usage frame parsed hRead table hTable index hIndex⟩
  rw [run_state,runWithWork_state,hValue]
  simp only [List.getElem?_eq_getElem (by rw [Array.length_toList,table.size]; exact j.isLt),Array.getElem_toList,FixedArrayTable.read]

noncomputable def heapPolynomial : Polynomial ℕ := 4*Polynomial.X*(9*Polynomial.X+23)
noncomputable def slotsPolynomial : Polynomial ℕ := Polynomial.X*(2*(heapPolynomial+1)+1)
noncomputable def preparationPolynomial : Polynomial ℕ :=
  Polynomial.X*(33*(100*(heapPolynomial+1)^2)+64)+1024*(Polynomial.X*(heapPolynomial+1)+Polynomial.X+1)+128
noncomputable def slotReadPolynomial : Polynomial ℕ :=
  128*(slotsPolynomial+1)*(slotsPolynomial+(Polynomial.X+1)+2)
noncomputable def heapReadPolynomial : Polynomial ℕ :=
  (heapPolynomial+1)*(5*((heapPolynomial+1)+1)+4)+8*heapPolynomial+10
noncomputable def readWorkPolynomial : Polynomial ℕ := slotReadPolynomial+heapReadPolynomial+8
noncomputable def readEnvelopePolynomial : Polynomial ℕ :=
  64*slotReadPolynomial+32*(heapReadPolynomial+heapPolynomial*(heapPolynomial+1)+2*heapPolynomial+5)+128

theorem preparation_is_polynomial : ∃ p : Polynomial ℕ,∀ L,p.eval L = preparationBound L := by
  refine ⟨preparationPolynomial,?_⟩
  intro L
  simp [preparationPolynomial,heapPolynomial,preparationBound,heapCap]

theorem readWork_is_polynomial : ∃ p : Polynomial ℕ,∀ L,p.eval L = readWorkBound L := by
  refine ⟨readWorkPolynomial,?_⟩
  intro L
  simp [readWorkPolynomial,slotReadPolynomial,heapReadPolynomial,heapPolynomial,slotsPolynomial,
    readWorkBound,BinaryReferenceVector.readBound,BinaryPRGWordStoreHeapMachine.readBound,
    BinaryPRGWordStoreHeapMachine.skipBound,heapCap,slotsCap]

theorem readEnvelope_is_polynomial : ∃ p : Polynomial ℕ,∀ L,p.eval L = PRGPhysicalArrayInterface.readEnvelope L := by
  refine ⟨readEnvelopePolynomial,?_⟩
  intro L
  simp [readEnvelopePolynomial,slotReadPolynomial,heapReadPolynomial,heapPolynomial,slotsPolynomial,
    PRGPhysicalArrayInterface.readEnvelope,BinaryReferenceVector.readBound,BinaryPRGWordStoreHeapMachine.readBound,
    BinaryPRGWordStoreHeapMachine.skipBound,heapCap,slotsCap]

theorem joined_bounds_are_polynomial :
    (∃ p : Polynomial ℕ,∀ L,p.eval L = preparationBound L+readWorkBound L+8) ∧
      (∃ p : Polynomial ℕ,∀ L,p.eval L = preparationBound L+PRGPhysicalArrayInterface.readEnvelope L+128) := by
  obtain ⟨p,hp⟩ := preparation_is_polynomial
  obtain ⟨w,hw⟩ := readWork_is_polynomial
  obtain ⟨s,hs⟩ := readEnvelope_is_polynomial
  exact ⟨⟨p+w+8,by intro L; simp [hp,hw]⟩,⟨p+s+128,by intro L; simp [hp,hs]⟩⟩

end Blotto.PRGPhysicalArrayRun
