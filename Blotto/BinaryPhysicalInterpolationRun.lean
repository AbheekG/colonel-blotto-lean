import Blotto.BinaryPhysicalInterpolationRow
import Blotto.BinaryPhysicalOutputLifetime
import Blotto.BinaryLifetimeListArray

/-! One physical interpolation run owns both prepared endpoint heaps, its
Boolean index stream and returned coordinate list. Native endpoint projection
and final native table packing are reserved by the selected-point caller. -/
namespace Blotto.BinaryPhysicalInterpolationRun
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option maxHeartbeats 4000000

def coordinates (scalar : SignedWord) (p q : List SignedWord) : List SignedWord :=
  (p.zip q).map (BinaryPhysicalInterpolationRow.coordinateData scalar)

theorem coordinates_length (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    (coordinates scalar p q).length = p.length := by
  simp only [coordinates,List.length_map,List.length_zip,← hLength,Nat.min_self]

def runWithTrace (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) : List SignedWord × Trace :=
  let first := BinaryWordObjectArrayLifetime.prepareWithTrace p
  let second := BinaryWordObjectArrayLifetime.prepareWithTrace q
  let indices := BooleanArrayIndexEnumeration.enumerateWithTrace p
  let row := BinaryPhysicalInterpolationRow.loopWithTrace first.1 second.1 scalar indices.1
  have hSome : row.1.isSome := by
    rw [BinaryPhysicalInterpolationRow.loop_enumerate first.1 second.1 p q
      (BinaryPhysicalOutputLifetime.prepared_realizes p) (BinaryPhysicalOutputLifetime.prepared_realizes q) hLength scalar]
    rfl
  (row.1.get hSome,wrap 64 2 [first.2,second.2,indices.2,row.2])

theorem run_state (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    (runWithTrace scalar p q hLength).1 = coordinates scalar p q := by
  unfold runWithTrace
  dsimp only
  exact Option.get_of_eq_some _ (BinaryPhysicalInterpolationRow.loop_enumerate _ _ p q
    (BinaryPhysicalOutputLifetime.prepared_realizes p) (BinaryPhysicalOutputLifetime.prepared_realizes q) hLength scalar)

theorem read_bound_at (words : List SignedWord) (n W I : ℕ) (hCount : words.length ≤ n)
    (hWords : ∀ word ∈ words,width word ≤ W) (hI : I ≤ n+1) :
    BinaryWordObjectArrayAccess.envelope (BinaryWordObjectArrayLifetime.prepareWithTrace words).1 I ≤
      BinaryPhysicalOutputLifetime.readEnvelope n W := by
  have hCaps := BinaryPhysicalOutputLifetime.store_caps words W hWords
  have hHeap : (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.heap.tape.length ≤ BinaryPhysicalOutputLifetime.heapCap n W := by
    apply hCaps.1.trans
    unfold BinaryPhysicalOutputLifetime.heapCap
    gcongr
  have hSlots : (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.slots.length ≤ BinaryPhysicalOutputLifetime.slotsCap n W := by
    apply hCaps.2.trans
    unfold BinaryPhysicalOutputLifetime.slotsCap BinaryPhysicalOutputLifetime.heapCap
    gcongr
  have hWidth := BinaryPhysicalOutputLifetime.wordWidth_le (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.heap.tape.length
  unfold BinaryWordObjectArrayAccess.envelope BinaryWordObjectArrayAccess.heapReadEnvelope
    BinaryPhysicalOutputLifetime.readEnvelope BinaryReferenceVector.readBound BinaryPRGWordStoreHeapMachine.readBound
    BinaryPRGWordStoreHeapMachine.skipBound
  gcongr <;> omega

def stepEnvelope (n W : ℕ) : ℕ := 2*BinaryPhysicalOutputLifetime.readEnvelope n W+BinaryPhysicalInterpolation.bound W+256

def bound (n W : ℕ) : ℕ := 2*BinaryPhysicalOutputLifetime.preparationBound n W+n*stepEnvelope n W+32*n+256

theorem run_usage (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length)
    (hT : BinaryRationalOpcode.Valid scalar) (W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    usage (runWithTrace scalar p q hLength).2 ≤ bound p.length W := by
  have hP := BinaryPhysicalOutputLifetime.preparation_bound p W (fun w hw => (hp w hw).2)
  have hQ' := BinaryPhysicalOutputLifetime.preparation_bound q W (fun w hw => (hq w hw).2)
  have hQ := hQ'.trans_eq (congrArg (fun N => BinaryPhysicalOutputLifetime.preparationBound N W) hLength.symm)
  have hIndices := BooleanArrayIndexEnumeration.enumerate_usage p
  have hWords : ∀ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace p).1,index.length ≤ p.length+1 := by
    intro index hi
    exact (BooleanArrayIndexEnumeration.enumerate_width p index hi).trans (BinaryPhysicalOutputLifetime.wordWidth_le p.length)
  have hLoop := BinaryPhysicalInterpolationRow.loop_usage (BinaryWordObjectArrayLifetime.prepareWithTrace p).1
    (BinaryWordObjectArrayLifetime.prepareWithTrace q).1 p q
    (BinaryPhysicalOutputLifetime.prepared_realizes p) (BinaryPhysicalOutputLifetime.prepared_realizes q)
    scalar hT (p.length+1) W hW ht hp hq (BooleanArrayIndexEnumeration.enumerateWithTrace p).1 hWords
  have hReadP := read_bound_at p p.length W (p.length+1) (by omega) (fun w hw => (hp w hw).2) (by omega)
  have hReadQ := read_bound_at q p.length W (p.length+1) hLength.symm.le (fun w hw => (hq w hw).2) (by omega)
  have hStep : BinaryPhysicalInterpolationRow.stepEnvelope (BinaryWordObjectArrayLifetime.prepareWithTrace p).1
      (BinaryWordObjectArrayLifetime.prepareWithTrace q).1 (p.length+1) W ≤ stepEnvelope p.length W := by
    unfold BinaryPhysicalInterpolationRow.stepEnvelope stepEnvelope
    omega
  have hLengthI : (BooleanArrayIndexEnumeration.enumerateWithTrace p).1.length = p.length := by
    have h := congrArg List.length (BooleanArrayIndexEnumeration.enumerate_values p)
    simpa only [List.length_map,List.length_range] using h
  rw [hLengthI] at hLoop
  have hLoop' := hLoop.trans (Nat.add_le_add_right (Nat.mul_le_mul_left p.length hStep) 32)
  have hw := wrap_usage 64 2 [(BinaryWordObjectArrayLifetime.prepareWithTrace p).2,
    (BinaryWordObjectArrayLifetime.prepareWithTrace q).2,(BooleanArrayIndexEnumeration.enumerateWithTrace p).2,
    (BinaryPhysicalInterpolationRow.loopWithTrace (BinaryWordObjectArrayLifetime.prepareWithTrace p).1
      (BinaryWordObjectArrayLifetime.prepareWithTrace q).1 scalar (BooleanArrayIndexEnumeration.enumerateWithTrace p).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace scalar p q hLength).2 ≤ _ at hw
  unfold bound
  omega

theorem all_prefix (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length)
    (hT : BinaryRationalOpcode.Valid scalar) (W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace scalar p q hLength).2 steps ≤ borrowed+bound p.length W ∧
      framePeak ((runWithTrace scalar p q hLength).2.take steps) ≤ bound p.length W :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_usage scalar p q hLength hT W hW ht hp hq) borrowed steps

end Blotto.BinaryPhysicalInterpolationRun
