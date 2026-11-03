import Blotto.BinaryThreeReferenceMeasured
import Blotto.BinaryNestedOrderLifetime

/-! Actual measured reference packing pads a nine-slot table, copies swapped
three-word rows and restores eighteen-slot tables. Source reference/control
charges and enlarged retained traces are explicit; native bit costs remain. -/
namespace Blotto.BinaryNestedReferenceMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 600000

abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def pad (table : BinaryStoredOverlapEnvironment.Segment 3 9) : (Segment × Trace) × ℕ :=
  let weights := BinaryThreeReferenceMeasured.references (α := SignedWord) 18
    (fun slot => Fin.addCases (n := 9) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot)
  let P := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 18
    (fun slot => Fin.addCases (n := 9) table.P.read (fun _ => table.P.read 0) slot)
  let Q := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 18
    (fun slot => Fin.addCases (n := 9) table.Q.read (fun _ => table.Q.read 0) slot)
  ((⟨weights.1.1,P.1.1,Q.1.1⟩,wrap 32 2 [weights.1.2,P.1.2,Q.1.2]),weights.2+P.2+Q.2+8)

theorem pad_data (table : BinaryStoredOverlapEnvironment.Segment 3 9) :
    (pad table).1.1 = (BinaryNestedBoundaryLifetime.padWithTrace table).1 := by
  simp only [pad,BinaryNestedBoundaryLifetime.padWithTrace,BinaryThreeReferenceMeasured.references_data,BinaryLifetimeArray.build_erases]

theorem pad_bounds (table : BinaryStoredOverlapEnvironment.Segment 3 9) :
    (pad table).2 ≤ 70000 ∧ usage (pad table).1.2 ≤ 36000 := by
  let weights := BinaryThreeReferenceMeasured.references (α := SignedWord) 18
    (fun slot => Fin.addCases (n := 9) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot)
  let P := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 18
    (fun slot => Fin.addCases (n := 9) table.P.read (fun _ => table.P.read 0) slot)
  let Q := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 18
    (fun slot => Fin.addCases (n := 9) table.Q.read (fun _ => table.Q.read 0) slot)
  have hwW : weights.2 ≤ 23176 := BinaryThreeReferenceMeasured.references_work 18 _
  have hpW : P.2 ≤ 23176 := BinaryThreeReferenceMeasured.references_work 18 _
  have hqW : Q.2 ≤ 23176 := BinaryThreeReferenceMeasured.references_work 18 _
  have hwU : usage weights.1.2 ≤ 11807 := BinaryThreeReferenceMeasured.references_usage 18 _
  have hpU : usage P.1.2 ≤ 11807 := BinaryThreeReferenceMeasured.references_usage 18 _
  have hqU : usage Q.1.2 ≤ 11807 := BinaryThreeReferenceMeasured.references_usage 18 _
  have hWrap := wrap_usage 32 2 [weights.1.2,P.1.2,Q.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change weights.2+P.2+Q.2+8 ≤ _ ∧ usage (wrap 32 2 [weights.1.2,P.1.2,Q.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

def swapRows (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) :
    (FixedArrayTable 18 (FixedArrayTable 3 SignedWord) × Trace) × ℕ :=
  BinaryLifetimeArrayMeasured.build 18 (fun slot => BinaryThreeReferenceMeasured.references 3
    ![(rows.read slot).read 1,(rows.read slot).read 0,(rows.read slot).read 2])

theorem swapRows_data (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) :
    (swapRows rows).1.1 = (BinaryNestedOrderLifetime.swapRowsWithTrace rows).1 := by
  simp only [swapRows,BinaryNestedOrderLifetime.swapRowsWithTrace,BinaryLifetimeArrayMeasured.build_data,
    BinaryLifetimeArray.build_erases,BinaryThreeReferenceMeasured.references_data,BinaryThreeReferenceLifetime.rowWithTrace]

theorem swapRows_bounds (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) :
    (swapRows rows).2 ≤ 42000 ∧ usage (swapRows rows).1.2 ≤ 24000 := by
  have hW := BinaryLifetimeArrayMeasured.build_work_bound 18
    (fun slot => BinaryThreeReferenceMeasured.references 3 ![(rows.read slot).read 1,(rows.read slot).read 0,(rows.read slot).read 2])
    1036 (fun _ => BinaryThreeReferenceMeasured.references_work 3 _)
  have hU := BinaryLifetimeArrayMeasured.build_bounds 18
    (fun slot => BinaryThreeReferenceMeasured.references 3 ![(rows.read slot).read 1,(rows.read slot).read 0,(rows.read slot).read 2]) 617 617
    (by intro slot; have h := BinaryThreeReferenceMeasured.references_usage 3
          ![(rows.read slot).read 1,(rows.read slot).read 0,(rows.read slot).read 2]; change _ ≤ 617 at h; unfold usage at h; omega)
    (by intro slot; have h := BinaryThreeReferenceMeasured.references_usage 3
          ![(rows.read slot).read 1,(rows.read slot).read 0,(rows.read slot).read 2]; change _ ≤ 617 at h; unfold usage at h; omega)
  change (swapRows rows).2 ≤ _ at hW
  change usage (swapRows rows).1.2 ≤ _ at hU
  norm_num only [BinaryLifetimeArrayMeasured.storageReserve] at hW hU
  exact ⟨by omega,by omega⟩

def swap (table : Segment) : (Segment × Trace) × ℕ :=
  let first := swapRows table.P
  let second := swapRows table.Q
  ((⟨table.weight,first.1.1,second.1.1⟩,wrap 32 2 [first.1.2,second.1.2]),first.2+second.2+8)

theorem swap_data (table : Segment) : (swap table).1.1 = BinaryNestedSpecProfile.swap table := by
  simp only [swap,swapRows_data,BinaryNestedOrderLifetime.swapRowsWithTrace_erasure,BinaryNestedSpecProfile.swap]

theorem swap_bounds (table : Segment) : (swap table).2 ≤ 85000 ∧ usage (swap table).1.2 ≤ 50000 := by
  have hp := swapRows_bounds table.P
  have hq := swapRows_bounds table.Q
  have hw := wrap_usage 32 2 [(swapRows table.P).1.2,(swapRows table.Q).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change (swapRows table.P).2+(swapRows table.Q).2+8 ≤ _ ∧ usage (wrap 32 2 [_,_]) ≤ _
  exact ⟨by omega,by omega⟩

def restore {α : Type*} (ordered : Bool) (prior : (α × Trace) × ℕ) (child : (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  if ordered then ((child.1.1,wrap 32 2 [prior.1.2,child.1.2]),prior.2+child.2+8) else
    let restored := swap child.1.1
    ((restored.1.1,wrap 32 2 [prior.1.2,child.1.2,restored.1.2]),prior.2+child.2+restored.2+12)

theorem restore_data {α : Type*} (ordered : Bool) (prior : (α × Trace) × ℕ) (child : (Segment × Trace) × ℕ) :
    (restore ordered prior child).1.1 = if ordered then child.1.1 else BinaryNestedSpecProfile.swap child.1.1 := by
  cases ordered <;> simp only [restore,Bool.false_eq_true,ite_false,ite_true,swap_data]

theorem restore_bounds {α : Type*} (ordered : Bool) (prior : (α × Trace) × ℕ) (child : (Segment × Trace) × ℕ)
    (C H B F : ℕ) (hC : prior.2 ≤ C ∧ usage prior.1.2 ≤ B) (hH : child.2 ≤ H ∧ usage child.1.2 ≤ F) :
    (restore ordered prior child).2 ≤ C+H+85000+16 ∧ usage (restore ordered prior child).1.2 ≤ B+F+50000+96 := by
  have hSwap := swap_bounds child.1.1
  unfold restore
  split
  · have hw := wrap_usage 32 2 [prior.1.2,child.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prior.2+child.2+8 ≤ _ ∧ usage (wrap 32 2 [prior.1.2,child.1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · have hw := wrap_usage 32 2 [prior.1.2,child.1.2,(swap child.1.1).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prior.2+child.2+(swap child.1.1).2+12 ≤ _ ∧ usage (wrap 32 2 [prior.1.2,child.1.2,(swap child.1.1).1.2]) ≤ _
    exact ⟨by omega,by omega⟩

end Blotto.BinaryNestedReferenceMeasured
