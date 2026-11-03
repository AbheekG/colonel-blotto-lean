import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryQuadraticSyntaxMeasured
import Blotto.BinaryThreeReferenceMeasured
import Blotto.BinaryOverlapGluingLifetime

/-! Measured sixteen-word environments feed all nine selected overlap programs.
Returned slot records are retained and projected into the actual descriptor
arrays through measured source packing. Exact old descriptor data is retained;
native label/reference/observer/allocator prices remain separate. -/

namespace Blotto.BinaryOverlapGluingMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryStoredOverlapEnvironment BinarySyntaxUniformWork
set_option autoImplicit false
set_option maxHeartbeats 400000

def environment {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : (FixedArrayTable 16 SignedWord × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.references 16
    ![(first.P.read i).read 0,(first.P.read i).read 1,(first.P.read i).read 2,
      (first.Q.read i).read 0,(first.Q.read i).read 1,(first.Q.read i).read 2,
      (second.P.read j).read 0,(second.P.read j).read 1,(second.P.read j).read 2,
      (second.Q.read j).read 0,(second.Q.read j).read 1,(second.Q.read j).read 2,
      first.weight.read i,second.weight.read j,interval,budget]

theorem environment_data {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    (environment first second interval budget i j).1.1 = BinaryStoredOverlapEnvironment.environment first second interval budget i j :=
  BinaryThreeReferenceMeasured.references_data _ _

def collect (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) (weight : (SignedWord × Trace) × ℕ)
    (p q : (FixedArrayTable 4 SignedWord × Trace) × ℕ) :
    ((SignedWord × FixedArrayTable 4 SignedWord × FixedArrayTable 4 SignedWord) × Trace) × ℕ :=
  (((weight.1.1,p.1.1,q.1.1),wrap 64 4 [env.1.2,weight.1.2,p.1.2,q.1.2]),env.2+weight.2+p.2+q.2+12)

set_option cleanup.letToHave false in
def fromEnvironmentWithExtras (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) : (((SignedWord × FixedArrayTable 4 SignedWord × FixedArrayTable 4 SignedWord) × Trace) × ℕ) × ℕ :=
  let weight := BinaryQuadraticSyntaxMeasured.runWithExtras env.1.1 BinaryOverlapCompilerBridge.weight
  let p := BinaryLifetimeArrayExtras.build 4 (fun r => BinaryQuadraticSyntaxMeasured.runWithExtras env.1.1 (BinaryOverlapCompilerBridge.safeP r))
  let q := BinaryLifetimeArrayExtras.build 4 (fun r => BinaryQuadraticSyntaxMeasured.runWithExtras env.1.1 (BinaryOverlapCompilerBridge.safeQ r))
  (collect env weight.1 p.1 q.1,weight.2+p.2+q.2)

def fromEnvironment (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) :
    ((SignedWord × FixedArrayTable 4 SignedWord × FixedArrayTable 4 SignedWord) × Trace) × ℕ :=
  (fromEnvironmentWithExtras env).1

theorem fromEnvironmentWithExtras_compat (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) :
    (fromEnvironmentWithExtras env).1 = fromEnvironment env := rfl

theorem fromEnvironment_record (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) :
    fromEnvironment env =
  let weight := BinaryQuadraticSyntaxMeasured.run env.1.1 BinaryOverlapCompilerBridge.weight
  let p := BinaryLifetimeArrayMeasured.build 4 (fun r => BinaryQuadraticSyntaxMeasured.run env.1.1 (BinaryOverlapCompilerBridge.safeP r))
  let q := BinaryLifetimeArrayMeasured.build 4 (fun r => BinaryQuadraticSyntaxMeasured.run env.1.1 (BinaryOverlapCompilerBridge.safeQ r))
  collect env weight p q := by
  simp only [fromEnvironment,fromEnvironmentWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat]

theorem fromEnvironment_eq (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) :
    fromEnvironment env = collect env
      (BinaryQuadraticSyntaxMeasured.run env.1.1 BinaryOverlapCompilerBridge.weight)
      (BinaryLifetimeArrayMeasured.build 4 (fun r => BinaryQuadraticSyntaxMeasured.run env.1.1 (BinaryOverlapCompilerBridge.safeP r)))
      (BinaryLifetimeArrayMeasured.build 4 (fun r => BinaryQuadraticSyntaxMeasured.run env.1.1 (BinaryOverlapCompilerBridge.safeQ r))) := fromEnvironment_record env


set_option cleanup.letToHave false in
def slotWithExtras {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : (((SignedWord × FixedArrayTable 4 SignedWord × FixedArrayTable 4 SignedWord) × Trace) × ℕ) × ℕ :=
  fromEnvironmentWithExtras (environment first second interval budget i j)

def slot {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    ((SignedWord × FixedArrayTable 4 SignedWord × FixedArrayTable 4 SignedWord) × Trace) × ℕ :=
  (slotWithExtras first second interval budget i j).1

theorem slotWithExtras_compat {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    (slotWithExtras first second interval budget i j).1 = slot first second interval budget i j := rfl

theorem slot_record {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    slot first second interval budget i j =
  fromEnvironment (environment first second interval budget i j) := by
  simp only [slot,slotWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,fromEnvironmentWithExtras_compat]

theorem slot_data {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    (slot first second interval budget i j).1.1 = (BinaryOverlapGluingLifetime.slotWithTrace first second interval budget i j).1 := by
  simp only [slot_record,fromEnvironment_record,collect,BinaryOverlapGluingLifetime.slotWithTrace,BinaryOverlapGluingLifetime.environmentWithTrace,
    environment_data,BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticSyntaxMeasured.run_erases]

set_option cleanup.letToHave false in
def descriptorWithExtras {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) : ((Segment 4 (k*h) × Trace) × ℕ) × ℕ :=
  let slots := BinaryLifetimeArrayExtras.build (k*h) (fun index =>
    let pair := finProdFinEquiv.symm index
    slotWithExtras first second interval budget pair.1 pair.2)
  let weight := BinaryThreeReferenceMeasured.references (k*h) (fun index => (slots.1.1.1.read index).1)
  let p := BinaryThreeReferenceMeasured.references (k*h) (fun index => (slots.1.1.1.read index).2.1)
  let q := BinaryThreeReferenceMeasured.references (k*h) (fun index => (slots.1.1.1.read index).2.2)
  (((⟨weight.1.1,p.1.1,q.1.1⟩,wrap 64 4 [slots.1.1.2,weight.1.2,p.1.2,q.1.2]),slots.1.2+weight.2+p.2+q.2+16),slots.2)

def descriptor {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) : (Segment 4 (k*h) × Trace) × ℕ :=
  (descriptorWithExtras first second interval budget).1

theorem descriptorWithExtras_compat {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) :
    (descriptorWithExtras first second interval budget).1 = descriptor first second interval budget := rfl

theorem descriptor_record {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) :
    descriptor first second interval budget =
  let slots := BinaryLifetimeArrayMeasured.build (k*h) (fun index =>
    let pair := finProdFinEquiv.symm index
    slot first second interval budget pair.1 pair.2)
  let weight := BinaryThreeReferenceMeasured.references (k*h) (fun index => (slots.1.1.read index).1)
  let p := BinaryThreeReferenceMeasured.references (k*h) (fun index => (slots.1.1.read index).2.1)
  let q := BinaryThreeReferenceMeasured.references (k*h) (fun index => (slots.1.1.read index).2.2)
  ((⟨weight.1.1,p.1.1,q.1.1⟩,wrap 64 4 [slots.1.2,weight.1.2,p.1.2,q.1.2]),slots.2+weight.2+p.2+q.2+16) := by
  simp only [descriptor,descriptorWithExtras,BinaryLifetimeArrayExtras.build_record,slotWithExtras_compat]

theorem descriptor_data {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord) :
    (descriptor first second interval budget).1.1 = (BinaryOverlapGluingLifetime.descriptorWithTrace first second interval budget).1 := by
  simp only [descriptor_record,BinaryOverlapGluingLifetime.descriptorWithTrace,BinaryThreeReferenceMeasured.references_data,
    BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases,slot_data,FixedArrayTable.read_ofFn]

def expressionWork (s : ℕ) : ℕ := BinaryQuadraticSyntaxMeasured.workEnvelope 256 256 s 16
def expressionCells (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.bound 256 256 s 16
def expressionFrames (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.frames 256 s 16
def slotPrice (s : ℕ) : ℕ := 9*expressionWork s+22000
def slotEnvelope (s : ℕ) : ℕ := 32*(expressionCells s+expressionFrames s+1000)
def workEnvelope (n s : ℕ) : ℕ := n*slotPrice s+256*(n+1)^2+12*n+16
def envelope (n s : ℕ) : ℕ := (n+1)*slotEnvelope s+4*BinaryLifetimeArrayMeasured.storageReserve n+32*n+128

theorem collect_bounds (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) (weight : (SignedWord × Trace) × ℕ)
    (p q : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (E B F : ℕ)
    (heW : env.2 ≤ 18560) (heU : usage env.1.2 ≤ 9483)
    (hwW : weight.2 ≤ E) (hwU : usage weight.1.2 ≤ B+F)
    (hpW : p.2 ≤ 4*E+1600) (hqW : q.2 ≤ 4*E+1600)
    (hpU : usage p.1.2 ≤ 4*B+F+882) (hqU : usage q.1.2 ≤ 4*B+F+882) :
    (collect env weight p q).2 ≤ 9*E+22000 ∧ usage (collect env weight p q).1.2 ≤ 32*(B+F+1000) := by
  have hw := wrap_usage 64 4 [env.1.2,weight.1.2,p.1.2,q.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change env.2+weight.2+p.2+q.2+12 ≤ _ ∧ usage (wrap 64 4 [env.1.2,weight.1.2,p.1.2,q.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromEnvironment_bounds (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ)
    (hEnvW : env.2 ≤ 18560) (hEnvU : usage env.1.2 ≤ 9483)
    (hC : ∀ r,CanonicalWord (env.1.1.read r)) (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env.1.1 s) :
    (fromEnvironment env).2 ≤ slotPrice s ∧ usage (fromEnvironment env).1.2 ≤ slotEnvelope s := by
  let original := env.1.1
  let weight := BinaryQuadraticSyntaxMeasured.run original BinaryOverlapCompilerBridge.weight
  let p := BinaryLifetimeArrayMeasured.build 4 (fun r => BinaryQuadraticSyntaxMeasured.run original (BinaryOverlapCompilerBridge.safeP r))
  let q := BinaryLifetimeArrayMeasured.build 4 (fun r => BinaryQuadraticSyntaxMeasured.run original (BinaryOverlapCompilerBridge.safeQ r))
  have hwgt := BinaryQuadraticSyntaxMeasured.run_work original BinaryOverlapCompilerBridge.weight hC s 16 256 256 hs hH
    BinaryOverlapGluingLifetime.weight_sizes.1 BinaryOverlapGluingLifetime.weight_sizes.2.1 BinaryOverlapGluingLifetime.weight_sizes.2.2
  have hwgtU := BinaryQuadraticSyntaxMeasured.run_bounds original BinaryOverlapCompilerBridge.weight hC s 16 256 256 hs hH
    BinaryOverlapGluingLifetime.weight_sizes.1 BinaryOverlapGluingLifetime.weight_sizes.2.1 BinaryOverlapGluingLifetime.weight_sizes.2.2
  have hpw := fun r => BinaryQuadraticSyntaxMeasured.run_work original (BinaryOverlapCompilerBridge.safeP r) hC s 16 256 256 hs hH
    (BinaryOverlapGluingLifetime.safeP_sizes r).1 (BinaryOverlapGluingLifetime.safeP_sizes r).2.1 (BinaryOverlapGluingLifetime.safeP_sizes r).2.2
  have hqw := fun r => BinaryQuadraticSyntaxMeasured.run_work original (BinaryOverlapCompilerBridge.safeQ r) hC s 16 256 256 hs hH
    (BinaryOverlapGluingLifetime.safeQ_sizes r).1 (BinaryOverlapGluingLifetime.safeQ_sizes r).2.1 (BinaryOverlapGluingLifetime.safeQ_sizes r).2.2
  have hpu := fun r => BinaryQuadraticSyntaxMeasured.run_bounds original (BinaryOverlapCompilerBridge.safeP r) hC s 16 256 256 hs hH
    (BinaryOverlapGluingLifetime.safeP_sizes r).1 (BinaryOverlapGluingLifetime.safeP_sizes r).2.1 (BinaryOverlapGluingLifetime.safeP_sizes r).2.2
  have hqu := fun r => BinaryQuadraticSyntaxMeasured.run_bounds original (BinaryOverlapCompilerBridge.safeQ r) hC s 16 256 256 hs hH
    (BinaryOverlapGluingLifetime.safeQ_sizes r).1 (BinaryOverlapGluingLifetime.safeQ_sizes r).2.1 (BinaryOverlapGluingLifetime.safeQ_sizes r).2.2
  have hPW := BinaryLifetimeArrayMeasured.build_work_bound 4 (fun r => BinaryQuadraticSyntaxMeasured.run original (BinaryOverlapCompilerBridge.safeP r)) (expressionWork s) hpw
  have hQW := BinaryLifetimeArrayMeasured.build_work_bound 4 (fun r => BinaryQuadraticSyntaxMeasured.run original (BinaryOverlapCompilerBridge.safeQ r)) (expressionWork s) hqw
  have hPU := BinaryLifetimeArrayMeasured.build_bounds 4 (fun r => BinaryQuadraticSyntaxMeasured.run original (BinaryOverlapCompilerBridge.safeP r))
    (expressionCells s) (expressionFrames s) (fun r => (hpu r).1) (fun r => (hpu r).2)
  have hQU := BinaryLifetimeArrayMeasured.build_bounds 4 (fun r => BinaryQuadraticSyntaxMeasured.run original (BinaryOverlapCompilerBridge.safeQ r))
    (expressionCells s) (expressionFrames s) (fun r => (hqu r).1) (fun r => (hqu r).2)
  have hWeightU : usage weight.1.2 ≤ expressionCells s+expressionFrames s := by
    unfold usage
    exact Nat.add_le_add hwgtU.1 hwgtU.2
  change weight.2 ≤ expressionWork s at hwgt
  change p.2 ≤ _ at hPW
  change q.2 ≤ _ at hQW
  change usage p.1.2 ≤ _ at hPU
  change usage q.1.2 ≤ _ at hQU
  have hPUEq : 4*expressionCells s+BinaryLifetimeArrayMeasured.storageReserve 4+2*4+expressionFrames s+10 =
      4*expressionCells s+expressionFrames s+882 := by unfold BinaryLifetimeArrayMeasured.storageReserve; omega
  have hPU' := hPU.trans_eq hPUEq
  have hQU' := hQU.trans_eq hPUEq
  have hCollected := collect_bounds env weight p q (expressionWork s) (expressionCells s) (expressionFrames s)
    hEnvW hEnvU hwgt hWeightU hPW hQW hPU' hQU'
  rw [fromEnvironment_eq]
  simpa only [weight,p,q,original,slotPrice,slotEnvelope] using hCollected

theorem slot_bounds {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord) (i : Fin k) (j : Fin h)
    (hFirst : first.Canonical) (hSecond : second.Canonical) (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight (BinaryStoredOverlapEnvironment.environment first second interval budget i j) s) :
    (slot first second interval budget i j).2 ≤ slotPrice s ∧ usage (slot first second interval budget i j).1.2 ≤ slotEnvelope s := by
  rw [slot_record]
  apply fromEnvironment_bounds
  · exact BinaryThreeReferenceMeasured.references_work 16 _
  · exact BinaryThreeReferenceMeasured.references_usage 16 _
  · rw [environment_data]
    exact environment_canonical first second interval budget i j hFirst hSecond hInterval hBudget
  · exact hs
  · rw [environment_data]
    exact hH

theorem descriptor_bounds {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord)
    (hFirst : first.Canonical) (hSecond : second.Canonical) (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s) (hH : ∀ i j,EnvHeight (BinaryStoredOverlapEnvironment.environment first second interval budget i j) s) :
    (descriptor first second interval budget).2 ≤ workEnvelope (k*h) s ∧
      usage (descriptor first second interval budget).1.2 ≤ envelope (k*h) s := by
  let n := k*h
  let slots := BinaryLifetimeArrayMeasured.build n (fun index =>
    slot first second interval budget (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)
  let weight := BinaryThreeReferenceMeasured.references n (fun index => (slots.1.1.read index).1)
  let p := BinaryThreeReferenceMeasured.references n (fun index => (slots.1.1.read index).2.1)
  let q := BinaryThreeReferenceMeasured.references n (fun index => (slots.1.1.read index).2.2)
  have hEach := fun index : Fin n => slot_bounds first second interval budget
    (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2 hFirst hSecond hInterval hBudget s hs (hH _ _)
  have hSlotsW := BinaryLifetimeArrayMeasured.build_work_bound n
    (fun index => slot first second interval budget (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)
    (slotPrice s) (fun index => (hEach index).1)
  have hSlotsU := BinaryLifetimeArrayMeasured.build_bounds n
    (fun index => slot first second interval budget (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)
    (slotEnvelope s) (slotEnvelope s)
    (by intro index; have h := (hEach index).2; unfold usage at h; omega)
    (by intro index; have h := (hEach index).2; unfold usage at h; omega)
  have hWW := BinaryThreeReferenceMeasured.references_work n (fun index => (slots.1.1.read index).1)
  have hPW := BinaryThreeReferenceMeasured.references_work n (fun index => (slots.1.1.read index).2.1)
  have hQW := BinaryThreeReferenceMeasured.references_work n (fun index => (slots.1.1.read index).2.2)
  have hWU := BinaryThreeReferenceMeasured.references_usage n (fun index => (slots.1.1.read index).1)
  have hPU := BinaryThreeReferenceMeasured.references_usage n (fun index => (slots.1.1.read index).2.1)
  have hQU := BinaryThreeReferenceMeasured.references_usage n (fun index => (slots.1.1.read index).2.2)
  change slots.2 ≤ _ at hSlotsW
  change usage slots.1.2 ≤ _ at hSlotsU
  change weight.2 ≤ _ at hWW
  change p.2 ≤ _ at hPW
  change q.2 ≤ _ at hQW
  change usage weight.1.2 ≤ _ at hWU
  change usage p.1.2 ≤ _ at hPU
  change usage q.1.2 ≤ _ at hQU
  have hw := wrap_usage 64 4 [slots.1.2,weight.1.2,p.1.2,q.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [descriptor_record]
  change slots.2+weight.2+p.2+q.2+16 ≤ _ ∧ usage (wrap 64 4 [slots.1.2,weight.1.2,p.1.2,q.1.2]) ≤ _
  change _ ≤ workEnvelope n s ∧ _ ≤ envelope n s
  unfold workEnvelope envelope BinaryThreeReferenceMeasured.referenceWork BinaryThreeReferenceMeasured.referenceEnvelope at *
  exact ⟨by nlinarith,by nlinarith⟩

theorem all_prefix {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord)
    (hFirst : first.Canonical) (hSecond : second.Canonical) (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s) (hH : ∀ i j,EnvHeight (BinaryStoredOverlapEnvironment.environment first second interval budget i j) s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor first second interval budget).1.2 steps ≤ borrowed+envelope (k*h) s ∧
      framePeak ((descriptor first second interval budget).1.2.take steps) ≤ envelope (k*h) s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_bounds first second interval budget hFirst hSecond hInterval hBudget s hs hH).2 borrowed steps

end Blotto.BinaryOverlapGluingMeasured
