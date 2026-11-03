import Blotto.BinaryCanonicalTrimMeasured
import Blotto.BinaryDivisionStorageMeasured
import Blotto.BinaryRationalRawMeasured
import Blotto.BinaryNumericalReadbackPlan

/-! Actual canonical trimming shares tail-recursive reversals and their length
counters with allocation/storage/source production. Trim, restoring division
and raw arithmetic return final-depth block plans with exact old records.
Inner arithmetic/metadata/native and physical-space scopes remain explicit. -/
namespace Blotto.BinaryPrimitiveTracePlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset charge_refines)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def reverseFrom : List Bool → List Bool → ℕ → List Bool × ℕ
  | [],acc,count => (acc,count)
  | bit::rest,acc,count => reverseFrom rest (bit::acc) (count+1)

theorem reverse_data (bits acc : List Bool) (count : ℕ) :
    (reverseFrom bits acc count).1 = bits.reverse++acc := by
  induction bits generalizing acc count with
  | nil => rfl
  | cons bit rest ih => simp [reverseFrom,ih,List.reverse_cons,List.append_assoc]

theorem reverse_count (bits acc : List Bool) (count : ℕ) :
    (reverseFrom bits acc count).2 = count+bits.length := by
  induction bits generalizing acc count with
  | nil => rfl
  | cons bit rest ih => simp only [reverseFrom,ih,List.length_cons]; omega

theorem scan_positive (bits : List Bool) : 1 ≤ (BinaryCanonicalTrimMeasured.scan bits).2 := by
  cases bits with
  | nil => simp [BinaryCanonicalTrimMeasured.scan]
  | cons bit rest => cases bit <;> simp [BinaryCanonicalTrimMeasured.scan]

def trimProduced (bits : List Bool) : (((List Bool × ℕ) × ℕ) × ℕ) × ℕ :=
  let front := reverseFrom bits [] 0
  let scanned := BinaryCanonicalTrimMeasured.scan front.1
  let back := reverseFrom scanned.1.1 [] 0
  let allocated := front.2+back.2+scanned.1.2+2
  ((((back.1,allocated),2*front.2+3*scanned.2+2*back.2+2),
    2*front.2+2*back.2+scanned.1.2+allocated+2),front.2)

theorem trimProduced_compat (bits : List Bool) :
    (trimProduced bits).1 = BinaryCanonicalTrimMeasured.stored bits := by
  simp only [trimProduced,BinaryCanonicalTrimMeasured.stored,reverse_data,reverse_count,
    List.append_nil,Nat.zero_add,List.length_reverse,two_mul,Nat.add_assoc]

theorem trimProduced_input (bits : List Bool) : (trimProduced bits).2 = bits.length := by
  simp only [trimProduced,reverse_count,Nat.zero_add]

def trimStored (bits : List Bool) : ((List Bool × ℕ) × ℕ) × ℕ := (trimProduced bits).1

theorem trimStored_exact (bits : List Bool) : trimStored bits = BinaryCanonicalTrimMeasured.stored bits :=
  trimProduced_compat bits

theorem trim_pays_reached_cases (bits : List Bool) :
    let front := reverseFrom bits [] 0
    let scanned := BinaryCanonicalTrimMeasured.scan front.1
    let back := reverseFrom scanned.1.1 [] 0
    front.2+1+scanned.2+back.2+1+1 ≤ (trimProduced bits).1.1.2 := by
  have h := scan_positive (reverseFrom bits [] 0).1
  dsimp only [trimProduced]
  omega

def trimAt (bits : List Bool) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let produced := trimProduced bits
  let result := produced.1
  ((result.1.1.1,.block [.frames (depth+(2*produced.2+8)),.arrayAllocation 8,
    .listAllocation result.2]),result.1.2)

theorem trim_refines (bits : List Bool) (depth : ℕ) :
    view (trimAt bits depth) = offset depth (BinaryCanonicalTrimMeasured.traced bits) := by
  simp only [trimAt,view,offset,denote,trimProduced_compat,trimProduced_input,
    BinaryCanonicalTrimMeasured.traced,under,shiftEvent,List.map_cons,List.map_nil]

theorem trim_budget (bits : List Bool) (depth : ℕ) : Bounded (trimAt bits depth).1.2 := by
  simp [trimAt,Bounded,nodes,payload]

theorem trim_work_bound (bits : List Bool) (depth : ℕ) : (trimAt bits depth).2 ≤ 7*bits.length+5 := by
  rw [charge_refines (trim_refines bits depth)]
  exact BinaryCanonicalTrimMeasured.traced_bound bits

def divideAt (dividend divisor : List Bool) (depth : ℕ) :
    ((List Bool × List Bool) × Plan) × (ℕ × ℕ) :=
  let produced := BinaryDivisionStorageMeasured.divideProduced dividend divisor
  let result := produced.1
  ((result.data,.block [.frames (depth+(produced.2.1+2*produced.2.2+16)),
    .arrayAllocation 8,.listAllocation result.storage]),(result.source,result.work))

theorem divide_refines (dividend divisor : List Bool) (depth : ℕ) :
    view (divideAt dividend divisor depth) = offset depth
      ((BinaryDivisionStorageMeasured.tracedMeasured dividend divisor).1.1,
        ((BinaryDivisionStorageMeasured.tracedMeasured dividend divisor).1.2,
          (BinaryDivisionStorageMeasured.tracedMeasured dividend divisor).2)) := by rfl

theorem divide_budget (dividend divisor : List Bool) (depth : ℕ) :
    Bounded (divideAt dividend divisor depth).1.2 := by
  simp [divideAt,Bounded,nodes,payload]

theorem divide_work_bound (dividend divisor : List Bool) (depth : ℕ) :
    (divideAt dividend divisor depth).2.2 ≤ 4*(divideAt dividend divisor depth).2.1 :=
  BinaryDivisionStorageMeasured.divide_work_bound dividend divisor

def rawAt (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) : (SignedWord × Plan) × ℕ :=
  let result := BinaryRationalRawStorageMeasured.apply op first second
  ((result.data,.block [.frames (depth+(result.allocated+8)),.arrayAllocation 16,
    .listAllocation result.storage]),result.work)

theorem raw_refines (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) :
    view (rawAt op first second depth) = offset depth (BinaryRationalRawMeasured.traced op first second) := by rfl

theorem raw_budget (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) :
    Bounded (rawAt op first second depth).1.2 := by
  simp [rawAt,Bounded,nodes,payload]

theorem raw_work_bound (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) :
    (rawAt op first second depth).2 ≤ 510*(BinaryRationalArithmetic.pairWidth first second+1)^2 :=
  BinaryRationalRawStorageMeasured.apply_work_bound op first second

end Blotto.BinaryPrimitiveTracePlan
