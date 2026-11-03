import Blotto.BinaryHeapAllocatorPlan
import Blotto.BinaryInitialWrapperEmission

/-! The reached allocator records feed both recursive children and their parent.
The plan is emitted once per prepared heap. Reference trees and charge observers
occur only in erased proofs; no logical shadow tree is retained. -/
namespace Blotto.BinaryHeapConstructionPlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryTracePlanMeasured BinaryPRGWordStoreHeap
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryPRGHeapStoredTree (Stored)
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def buildReference (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) :
    (Built × Trace) × Charge :=
  (((BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).1,
    (BinaryPRGHeapPreparationLifetime.buildWithTrace fallback ruler items heap).2),
    (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).2)

def buildAt (fallback : SignedWord) : List Bool → List SignedWord → Heap → ℕ → (Built × Plan) × Charge
  | [],[],heap,depth =>
      let produced := BinaryHeapAllocatorPlan.allocateAt heap (.leaf fallback) (depth+1)
      ((⟨produced.1.1.1,produced.1.1.2,[]⟩,
        .join (.block [.frames (depth+2),.arrayAllocation 16]) produced.1.2),produced.2.add ⟨4,4⟩)
  | [],word::rest,heap,depth =>
      let produced := BinaryHeapAllocatorPlan.allocateAt heap (.leaf word) (depth+1)
      ((⟨produced.1.1.1,produced.1.1.2,rest⟩,
        .join (.block [.frames (depth+2),.arrayAllocation 16]) produced.1.2),produced.2.add ⟨4,4⟩)
  | _::ruler,items,heap,depth =>
      let first := buildAt fallback ruler items heap (depth+1)
      let second := buildAt fallback ruler first.1.1.remaining first.1.1.heap (depth+1)
      let produced := BinaryHeapAllocatorPlan.allocateAt second.1.1.heap (.branch first.1.1.root second.1.1.root) (depth+1)
      ((⟨produced.1.1.1,produced.1.1.2,second.1.1.remaining⟩,
        .join (.block [.frames (depth+2),.arrayAllocation 24])
          (.join first.1.2 (.join second.1.2 produced.1.2))),
        first.2.add (second.2.add (produced.2.add ⟨8,8⟩)))

theorem build_refines (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) (depth : ℕ) :
    view (buildAt fallback ruler items heap depth) = offset depth (buildReference fallback ruler items heap) := by
  induction ruler generalizing items heap depth with
  | nil =>
      cases items <;> simp only [buildAt,buildReference,BinaryPRGWordStoreHeapMachine.buildWithWork,
        BinaryPRGHeapPreparationLifetime.buildWithTrace,view,offset,denote,
        BinaryHeapAllocatorPlan.allocate_data,BinaryHeapAllocatorPlan.allocate_trace,BinaryHeapAllocatorPlan.allocate_charge,
        BinaryPRGHeapAllocationLifetime.allocateWithTrace_erasure,under_append,under_compose,List.append_assoc] <;> rfl
  | cons bit ruler ih =>
      have hFirst := ih items heap (depth+1)
      have hSecond := ih (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).1.remaining
        (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).1.heap (depth+1)
      simp only [buildAt,buildReference,BinaryPRGWordStoreHeapMachine.buildWithWork,
        BinaryPRGHeapPreparationLifetime.buildWithTrace,view,offset,denote,
        data_refines hFirst,trace_refines hFirst,charge_refines hFirst,
        data_refines hSecond,trace_refines hSecond,charge_refines hSecond,
        BinaryHeapAllocatorPlan.allocate_data,BinaryHeapAllocatorPlan.allocate_trace,BinaryHeapAllocatorPlan.allocate_charge,
        BinaryPRGHeapPreparationLifetime.buildWithTrace_erasure,
        BinaryPRGHeapAllocationLifetime.allocateWithTrace_erasure,under_append,under_compose,List.append_assoc]
      rfl

theorem build_data (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) (depth : ℕ) :
    (buildAt fallback ruler items heap depth).1.1 = (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).1 :=
  data_refines (build_refines fallback ruler items heap depth)

theorem build_trace (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) (depth : ℕ) :
    denote (buildAt fallback ruler items heap depth).1.2 = under depth (BinaryPRGHeapPreparationLifetime.buildWithTrace fallback ruler items heap).2 :=
  trace_refines (build_refines fallback ruler items heap depth)

theorem build_charge (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) (depth : ℕ) :
    (buildAt fallback ruler items heap depth).2 = (BinaryPRGWordStoreHeapMachine.buildWithWork fallback ruler items heap).2 :=
  charge_refines (build_refines fallback ruler items heap depth)

theorem build_bound (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) (depth : ℕ) :
    Bounded (buildAt fallback ruler items heap depth).1.2 := by
  induction ruler generalizing items heap depth with
  | nil =>
      cases items with
      | nil =>
          have ha := BinaryHeapAllocatorPlan.allocate_bound heap (.leaf fallback) (depth+1)
          simp only [Bounded,buildAt,nodes,payload,List.length_cons,List.length_nil] at ha ⊢
          omega
      | cons word rest =>
          have ha := BinaryHeapAllocatorPlan.allocate_bound heap (.leaf word) (depth+1)
          simp only [Bounded,buildAt,nodes,payload,List.length_cons,List.length_nil] at ha ⊢
          omega
  | cons bit ruler ih =>
      let first := buildAt fallback ruler items heap (depth+1)
      let second := buildAt fallback ruler first.1.1.remaining first.1.1.heap (depth+1)
      have hf := ih items heap (depth+1)
      have hs := ih first.1.1.remaining first.1.1.heap (depth+1)
      have ha := BinaryHeapAllocatorPlan.allocate_bound second.1.1.heap (.branch first.1.1.root second.1.1.root) (depth+1)
      simp only [Bounded,buildAt,nodes,payload,List.length_cons,List.length_nil] at hf hs ha ⊢
      dsimp only [first,second] at hf hs ha
      omega

def prepareRulerAt (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (depth : ℕ) :
    (Stored (BinaryPRGWordControllerWordStore.build fallback ruler items).1 × Plan) × Charge :=
  let built := buildAt fallback ruler items empty (depth+2)
  ((⟨ruler,rfl,built.1.1.heap,built.1.1.root,
    (by rw [build_data,BinaryPRGWordStoreHeapMachine.buildWithWork_erasure]
        exact (build_contract fallback ruler items empty empty_valid).1),
    (by rw [build_data,BinaryPRGWordStoreHeapMachine.buildWithWork_erasure]
        exact (build_contract fallback ruler items empty empty_valid).2.2.1)⟩,
    .join (.block [.frames (depth+2),.arrayAllocation 16]) built.1.2),built.2)

def prepareReference (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :=
  (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace fallback ruler items,
    (BinaryPRGHeapStoredTree.prepareRulerWithWork fallback ruler items).2)

theorem prepare_refines (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (depth : ℕ) :
    view (prepareRulerAt fallback ruler items depth) = offset depth (prepareReference fallback ruler items) := by
  simp only [prepareRulerAt,prepareReference,BinaryPRGHeapRulerLifetime.prepareRulerWithTrace,
    BinaryPRGHeapStoredTree.prepareRulerWithWork,view,offset,denote,build_data,build_trace,build_charge,
    BinaryPRGHeapPreparationLifetime.buildWithTrace_erasure,wrap,combine,List.append_nil,under_append,under_compose]
  rfl

theorem prepare_bound (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (depth : ℕ) :
    Bounded (prepareRulerAt fallback ruler items depth).1.2 := by
  have h := build_bound fallback ruler items empty (depth+2)
  simp only [Bounded,prepareRulerAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def prepareWithEmission (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :=
  finish (prepareRulerAt fallback ruler items 0)

theorem prepare_compat (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    (prepareWithEmission fallback ruler items).1 = prepareReference fallback ruler items :=
  BinaryNumericalReadbackPlan.finish_compat (prepare_refines fallback ruler items 0)

theorem prepare_emission_bound (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    (prepareWithEmission fallback ruler items).2 ≤ 25*(prepareWithEmission fallback ruler items).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (prepare_bound fallback ruler items 0)

def countWithEmission {α : Type*} (items : List α) (counter : Pointer) :=
  finish (BinaryHeapAllocatorPlan.countAt items counter 0)

theorem count_compat {α : Type*} (items : List α) (counter : Pointer) :
    (countWithEmission items counter).1 = (BinaryPRGHeapAllocationLifetime.countWithTrace items counter,
      (BinaryPRGWordStoreHeapMachine.countWithWork items counter).2) := by
  rw [countWithEmission,BinaryNumericalReadbackPlan.finish_record,BinaryHeapAllocatorPlan.count_refines]
  apply Prod.ext
  · simpa only [under_zero] using BinaryHeapAllocationMeasured.countAt_erases items counter 0
  · exact BinaryHeapAllocationMeasured.countAt_charge items counter 0

theorem count_emission_bound {α : Type*} (items : List α) (counter : Pointer) :
    (countWithEmission items counter).2 ≤ 25*(countWithEmission items counter).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (BinaryHeapAllocatorPlan.count_bound items counter 0)

theorem count_value {α : Type*} (items : List α) (counter : Pointer) :
    (countWithEmission items counter).1.1.1 = (BinaryPRGHeapAllocationLifetime.countWithTrace items counter).1 :=
  congrArg (fun out => out.1.1) (count_compat items counter)

/-- The old root wrapper still runs. The added field prices the three reached
source records and their three emissions. The old encoded tree allowance may
also reserve the same build work, so their sum is a conservative upper bound. -/
def rawWithEmission (capacity resource : List SignedWord) :=
  let counted := countWithEmission capacity []
  let limits := prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 capacity
  let bids := prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 resource
  let emitted := BinaryInitialWrapperEmission.listThree (3*capacity.length) 64 (3*capacity.length+4)
    counted.1.1.2 limits.1.1.2 bids.1.1.2
  ((((⟨counted.1.1.1,(limits.1.1.1,bids.1.1.1)⟩ :
    Σ ruler, BinaryPhysicalHeapInputLifetime.RawArraysAt capacity resource ruler),emitted.1),emitted.2),
    counted.1.2.work+limits.1.2.work+bids.1.2.work+counted.2+limits.2+bids.2)

theorem raw_compat (capacity resource : List SignedWord) :
    (rawWithEmission capacity resource).1 = BinaryInitialWrapperEmission.rawArraysWithEmission capacity resource := by
  simp only [rawWithEmission,BinaryInitialWrapperEmission.rawArraysWithEmission,count_compat,prepare_compat,prepareReference,count_value]
  rw [count_value]

theorem raw_data (capacity resource : List SignedWord) :
    (rawWithEmission capacity resource).1.1 = BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource := by
  rw [raw_compat,BinaryInitialWrapperEmission.rawArraysWithEmission_compat]

theorem raw_bound (capacity resource : List SignedWord) :
    (rawWithEmission capacity resource).2 ≤
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork capacity resource).2+
      25*(rawWithEmission capacity resource).1.1.2.length+12*(capacity.length+1)^2 := by
  have hc := count_emission_bound capacity ([] : Pointer)
  have hl := prepare_emission_bound BinaryRationalOpcode.zero
    (countWithEmission capacity []).1.1.1 capacity
  have hr := prepare_emission_bound BinaryRationalOpcode.zero
    (countWithEmission capacity []).1.1.1 resource
  have hw := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork_covers_native capacity resource
  have hk := (BinaryPRGWordStoreHeapMachine.countWithWork_bounds capacity ([] : Pointer)).1
  simp only [count_compat,prepare_compat,prepareReference,count_value] at hc hl hr
  simp only [rawWithEmission,BinaryInitialWrapperEmission.listThree_length,count_compat,prepare_compat,prepareReference,count_value]
  rw [count_value] at hl hr ⊢
  unfold BinaryPRGWordStoreHeapMachine.countBound at hk
  dsimp only at hw hk
  simp only [List.length_nil,Nat.zero_add] at hk
  nlinarith only [hc,hl,hr,hw,hk]

theorem raw_allocated_bound (capacity resource : List SignedWord) :
    let counted := countWithEmission capacity []
    let limits := prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 capacity
    let bids := prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 resource
    counted.1.2.allocatedBits+limits.1.2.allocatedBits+bids.1.2.allocatedBits ≤
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork capacity resource).2+
      capacity.length*(capacity.length+1) := by
  have hw := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork_covers_native_allocated capacity resource
  have hk := (BinaryPRGWordStoreHeapMachine.countWithWork_bounds capacity ([] : Pointer)).2
  simp only [count_compat,prepare_compat,prepareReference,count_value]
  rw [count_value]
  dsimp only at hw hk
  simp only [List.length_nil,Nat.zero_add] at hk
  omega

end Blotto.BinaryHeapConstructionPlan
