import Blotto.BinarySteinTracePlan
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryPrimitiveTracePlan

/-! Actual planned GCD, restoring divisions, sign scan and trims feed one
normalization/canonicalization/opcode plan. Complete old measured records,
including division work, remain exact. Emission counts reached plan work;
primitive leaf/native/reference/physical-space scopes remain explicit. -/
namespace Blotto.BinaryNormalizationPlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded)
open BinarySteinTracePlan (scan_data scan_trace)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def normalizeAt (word : SignedWord) (depth : ℕ) : (SignedWord × Plan) × (ℕ × ℕ) :=
  let common := BinarySteinTracePlan.gcdAt word.numerator word.denominator (depth+2)
  let numerator := BinaryPrimitiveTracePlan.divideAt word.numerator common.1.1 (depth+2)
  let denominator := BinaryPrimitiveTracePlan.divideAt word.denominator common.1.1 (depth+2)
  let sign := BooleanFreshSeedMeasured.scanAt numerator.1.1.1 (depth+2)
  ((⟨word.negative && sign.1.1,numerator.1.1.1,denominator.1.1.1⟩,
    .join (.block [.frames (depth+2),.arrayAllocation 16])
      (.join common.1.2 (.join numerator.1.2 (.join denominator.1.2 (.block sign.1.2))))),
    (common.2+numerator.2.1+denominator.2.1+3*(word.numerator.length+1)+2,numerator.2.2+denominator.2.2))

theorem normalize_refines (word : SignedWord) (depth : ℕ) :
    view (normalizeAt word depth) = offset depth
      ((BinaryQuadraticMeasured.normalizeMeasured word).1.1,
        ((BinaryQuadraticMeasured.normalizeMeasured word).1.2,(BinaryQuadraticMeasured.normalizeMeasured word).2)) := by
  have h := BinarySteinTracePlan.gcd_refines word.numerator word.denominator (depth+2)
  have hn := BinaryPrimitiveTracePlan.divide_refines word.numerator
    (BinarySteinGCDMeasured.gcd word.numerator word.denominator).1.1 (depth+2)
  have hd := BinaryPrimitiveTracePlan.divide_refines word.denominator
    (BinarySteinGCDMeasured.gcd word.numerator word.denominator).1.1 (depth+2)
  simp only [normalizeAt,BinaryQuadraticMeasured.normalizeMeasured,view,offset,denote,
    data_refines hn,trace_refines hn,charge_refines hn,data_refines hd,trace_refines hd,charge_refines hd,
    data_refines h,trace_refines h,charge_refines h,scan_data,scan_trace,
    under_append,under_compose,List.append_assoc]
  rfl

theorem normalize_budget (word : SignedWord) (depth : ℕ) : Bounded (normalizeAt word depth).1.2 := by
  have h := BinarySteinTracePlan.gcd_budget word.numerator word.denominator (depth+2)
  simp only [normalizeAt,BinaryPrimitiveTracePlan.divideAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def canonicalizeAt (word : SignedWord) (depth : ℕ) : (SignedWord × Plan) × (ℕ × ℕ) :=
  let normalized := normalizeAt word (depth+2)
  let numerator := BinaryPrimitiveTracePlan.trimAt normalized.1.1.numerator (depth+2)
  let denominator := BinaryPrimitiveTracePlan.trimAt normalized.1.1.denominator (depth+2)
  ((⟨normalized.1.1.negative,numerator.1.1,denominator.1.1⟩,
    .join (.block [.frames (depth+2),.arrayAllocation 16])
      (.join normalized.1.2 (.join numerator.1.2 denominator.1.2))),
    (normalized.2.1+numerator.2+denominator.2,normalized.2.2))

theorem canonicalize_refines (word : SignedWord) (depth : ℕ) :
    view (canonicalizeAt word depth) = offset depth
      ((BinaryQuadraticMeasured.canonicalizeMeasured word).1.1,
        ((BinaryQuadraticMeasured.canonicalizeMeasured word).1.2,(BinaryQuadraticMeasured.canonicalizeMeasured word).2)) := by
  have h := normalize_refines word (depth+2)
  have hn := BinaryPrimitiveTracePlan.trim_refines
    (BinaryQuadraticMeasured.normalizeMeasured word).1.1.1.numerator (depth+2)
  have hd := BinaryPrimitiveTracePlan.trim_refines
    (BinaryQuadraticMeasured.normalizeMeasured word).1.1.1.denominator (depth+2)
  simp only [canonicalizeAt,BinaryQuadraticMeasured.canonicalizeMeasured,view,offset,denote,
    data_refines hn,trace_refines hn,charge_refines hn,data_refines hd,trace_refines hd,charge_refines hd,
    data_refines h,trace_refines h,charge_refines h,under_append,under_compose,List.append_assoc]
  rfl

theorem canonicalize_budget (word : SignedWord) (depth : ℕ) : Bounded (canonicalizeAt word depth).1.2 := by
  have h := normalize_budget word (depth+2)
  simp only [canonicalizeAt,BinaryPrimitiveTracePlan.trimAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def applyAt (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) : (SignedWord × Plan) × (ℕ × ℕ) :=
  let raw := BinaryPrimitiveTracePlan.rawAt op first second (depth+2)
  let canonical := canonicalizeAt raw.1.1 (depth+2)
  ((canonical.1.1,.join (.block [.frames (depth+2),.arrayAllocation 16])
    (.join raw.1.2 canonical.1.2)),(raw.2+canonical.2.1,canonical.2.2))

theorem apply_refines (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) :
    view (applyAt op first second depth) = offset depth
      ((BinaryQuadraticMeasured.applyMeasured op first second).1.1,
        ((BinaryQuadraticMeasured.applyMeasured op first second).1.2,(BinaryQuadraticMeasured.applyMeasured op first second).2)) := by
  have h := canonicalize_refines (BinaryRationalRawMeasured.traced op first second).1.1 (depth+2)
  have hr := BinaryPrimitiveTracePlan.raw_refines op first second (depth+2)
  simp only [applyAt,BinaryQuadraticMeasured.applyMeasured,view,offset,denote,
    data_refines hr,trace_refines hr,charge_refines hr,
    data_refines h,trace_refines h,charge_refines h,under_append,under_compose,List.append_assoc]
  rfl

theorem apply_budget (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) :
    Bounded (applyAt op first second depth).1.2 := by
  have h := canonicalize_budget (BinaryPrimitiveTracePlan.rawAt op first second (depth+2)).1.1 (depth+2)
  simp only [applyAt,BinaryPrimitiveTracePlan.rawAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def finishMeasured {α : Type*} (record : (α × Plan) × (ℕ × ℕ)) : (((α × Trace) × ℕ) × ℕ) × ℕ :=
  let produced := finish record
  (((produced.1.1,produced.1.2.1),produced.1.2.2),produced.2)

theorem finishMeasured_compat {α : Type*} {record : (α × Plan) × (ℕ × ℕ)} {old : ((α × Trace) × ℕ) × ℕ}
    (h : view record = offset 0 (old.1.1,(old.1.2,old.2))) : (finishMeasured record).1 = old := by
  have he := BinaryNumericalReadbackPlan.finish_compat h
  simp only [finishMeasured,he]

theorem finishMeasured_price {α : Type*} (record : (α × Plan) × (ℕ × ℕ)) (h : Bounded record.1.2) :
    (finishMeasured record).2 ≤ 25*(finishMeasured record).1.1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound record h

def normalize (word : SignedWord) := finishMeasured (normalizeAt word 0)

theorem normalize_compat (word : SignedWord) : (normalize word).1 = BinaryQuadraticMeasured.normalizeMeasured word :=
  finishMeasured_compat (normalize_refines word 0)

theorem normalize_price (word : SignedWord) : (normalize word).2 ≤ 25*(normalize word).1.1.1.2.length+5 :=
  finishMeasured_price (normalizeAt word 0) (normalize_budget word 0)

def canonicalize (word : SignedWord) := finishMeasured (canonicalizeAt word 0)

theorem canonicalize_compat (word : SignedWord) : (canonicalize word).1 = BinaryQuadraticMeasured.canonicalizeMeasured word :=
  finishMeasured_compat (canonicalize_refines word 0)

theorem canonicalize_price (word : SignedWord) : (canonicalize word).2 ≤ 25*(canonicalize word).1.1.1.2.length+5 :=
  finishMeasured_price (canonicalizeAt word 0) (canonicalize_budget word 0)

theorem canonicalize_division (word : SignedWord) : (canonicalize word).1.2 ≤ 4*(canonicalize word).1.1.2 := by
  have h := BinaryQuadraticMeasured.canonicalizeMeasured_division_work_bound word
  simp only [BinaryQuadraticMeasured.canonicalize] at h
  rw [canonicalize_compat]
  exact h

def apply (op : RealArithmeticOp) (first second : SignedWord) := finishMeasured (applyAt op first second 0)

theorem apply_compat (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).1 = BinaryQuadraticMeasured.applyMeasured op first second :=
  finishMeasured_compat (apply_refines op first second 0)

theorem apply_price (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).2 ≤ 25*(apply op first second).1.1.1.2.length+5 :=
  finishMeasured_price (applyAt op first second 0) (apply_budget op first second 0)

theorem apply_division (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).1.2 ≤ 4*(apply op first second).1.1.2 := by
  have h := BinaryQuadraticMeasured.applyMeasured_division_work_bound op first second
  simp only [BinaryQuadraticMeasured.apply] at h
  rw [apply_compat]
  exact h

theorem apply_contract (op : RealArithmeticOp) (first second : SignedWord)
    (hFirst : BinaryRationalOpcode.Valid first) (hSecond : BinaryRationalOpcode.Valid second) :
    value (apply op first second).1.1.1.1 = op.applyRat (value first) (value second) ∧
      BinaryRationalEncoding.CanonicalWord (apply op first second).1.1.1.1 ∧
      (apply op first second).1.1.2 ≤ 44000*RationalCostModel.schoolbook.rat
        (BinaryRationalArithmetic.pairWidth first second) := by
  rw [apply_compat]
  exact BinaryQuadraticMeasured.apply_contract op first second hFirst hSecond

end Blotto.BinaryNormalizationPlan
