import Blotto.BinaryTerminalPrefixLifetime
import Blotto.BinaryTracePlanMeasured

/-! Actual cache classification/next-fit packing retain their prior data and
source counters while building one final-depth trace plan. Primitive arithmetic
records keep their preceding scope; no prefix plan is emitted here. -/
namespace Blotto.BinaryCachePrefixPlan
open BinarySeedPreparationSpace BinaryTraceDepth BinaryTracePlanMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryTerminalPrefixLifetime
set_option autoImplicit false
set_option maxHeartbeats 2000000

def observe {α : Type*} (record : (α × Plan) × ℕ) : (α × Trace) × ℕ :=
  ((record.1.1,denote record.1.2),record.2)

def offset {α : Type*} (depth : ℕ) (record : (α × Trace) × ℕ) : (α × Trace) × ℕ :=
  ((record.1.1,under depth record.1.2),record.2)

theorem data_of_refinement {α : Type*} {produced : (α × Plan) × ℕ} {reference : (α × Trace) × ℕ} {depth : ℕ}
    (h : observe produced = offset depth reference) : produced.1.1 = reference.1.1 :=
  congrArg (fun record : (α × Trace) × ℕ => record.1.1) h

theorem trace_of_refinement {α : Type*} {produced : (α × Plan) × ℕ} {reference : (α × Trace) × ℕ} {depth : ℕ}
    (h : observe produced = offset depth reference) : denote produced.1.2 = under depth reference.1.2 :=
  congrArg (fun record : (α × Trace) × ℕ => record.1.2) h

theorem work_of_refinement {α : Type*} {produced : (α × Plan) × ℕ} {reference : (α × Trace) × ℕ} {depth : ℕ}
    (h : observe produced = offset depth reference) : produced.2 = reference.2 := congrArg Prod.snd h

def Bounded (plan : Plan) : Prop := nodes plan ≤ 4*payload plan+1

theorem block_bound (events : Trace) : Bounded (.block events) := by simp [Bounded,nodes,payload]

theorem shifted_bound (depth : ℕ) (events : Trace) : Bounded (.shifted depth events) := by simp [Bounded,nodes,payload]

def classificationAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    List (Fin n) → ℕ → (Classification n × Plan) × ℕ
  | [],depth => ((⟨[],none⟩,.block [.frames (depth+1),.arrayAllocation 8]),0)
  | j::rest,depth =>
      let resource := input.resource.read j
      let length := input.length.read j
      let upward := BinaryRationalOpcodeAllocation.lessEqualWithAllocation resource length
      let downward := BinaryRationalOpcodeAllocation.lessEqualWithAllocation length resource
      let nonpositive := BinaryRationalOpcodeAllocation.lessEqualWithAllocation resource zero
      let later := classificationAt input rest (depth+1)
      ((⟨if upward.1 && downward.1 then j::later.1.1.uniforms else later.1.1.uniforms,
        if (!nonpositive.1) && (!downward.1) then some j else later.1.1.pivot⟩,
        .join (.block [.frames (depth+1),.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage resource length),
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage length resource),
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage resource zero)]) later.1.2),
        BinaryRationalArithmetic.lessEqualWork resource length+
          BinaryRationalArithmetic.lessEqualWork length resource+
          BinaryRationalArithmetic.lessEqualWork resource zero+later.2)

theorem classification_refines {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) (depth : ℕ) :
    observe (classificationAt input items depth) = offset depth (classificationWithTraceAndWork input items) := by
  induction items generalizing depth with
  | nil => rfl
  | cons j rest ih =>
      have hd := data_of_refinement (ih (depth+1))
      have ht := trace_of_refinement (ih (depth+1))
      have hw := work_of_refinement (ih (depth+1))
      simp only [observe,offset,classificationAt,classificationWithTraceAndWork,denote,hd,ht,hw,
        under_append,under_compose]
      rfl

theorem classification_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) (depth : ℕ) :
    Bounded (classificationAt input items depth).1.2 := by
  induction items generalizing depth with
  | nil => exact block_bound _
  | cons j rest ih =>
      have h := ih (depth+1)
      simp only [Bounded,classificationAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

def packAuxAt {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → SignedWord → List α → ℕ → (List (List α × SignedWord) × Plan) × ℕ
  | current,total,[],depth =>
      (([(current.reverse,total)],.block [.frames (depth+(current.length+8)),
        .listAllocation (current.length+3),.arrayAllocation 8]),0)
  | current,total,item::rest,depth =>
      let added := BinaryRationalOpcodeAllocation.applyWithAllocation .add total (length item)
      let comparison := BinaryRationalOpcodeAllocation.lessEqualWithAllocation added.1 budget
      let localPlan := Plan.block [.frames (depth+(current.length+8)),.arrayAllocation 8,
        .listAllocation (current.length+4),
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .add total (length item)),
        .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage added.1 budget)]
      let localWork := (applyWithWork .add total (length item)).2+BinaryRationalArithmetic.lessEqualWork added.1 budget
      if comparison.1 then
        let later := packAuxAt length budget (item::current) added.1 rest (depth+1)
        ((later.1.1,.join localPlan later.1.2),localWork+later.2)
      else
        let later := packAuxAt length budget [item] (length item) rest (depth+1)
        (((current.reverse,total)::later.1.1,.join localPlan later.1.2),localWork+later.2)

theorem packAux_refines {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) (depth : ℕ) :
    observe (packAuxAt length budget current total rest depth) =
      offset depth (packAuxWithTraceAndWork length budget current total rest) := by
  induction rest generalizing current total depth with
  | nil => rfl
  | cons item rest ih =>
      unfold packAuxAt packAuxWithTraceAndWork
      dsimp only
      split
      · have hd := data_of_refinement (ih (item::current) (BinaryRationalOpcodeAllocation.applyWithAllocation .add total (length item)).1 (depth+1))
        have ht := trace_of_refinement (ih (item::current) (BinaryRationalOpcodeAllocation.applyWithAllocation .add total (length item)).1 (depth+1))
        have hw := work_of_refinement (ih (item::current) (BinaryRationalOpcodeAllocation.applyWithAllocation .add total (length item)).1 (depth+1))
        simp only [observe,offset,denote,hd,ht,hw,under_append,under_compose]
        rfl
      · have hd := data_of_refinement (ih [item] (length item) (depth+1))
        have ht := trace_of_refinement (ih [item] (length item) (depth+1))
        have hw := work_of_refinement (ih [item] (length item) (depth+1))
        simp only [observe,offset,denote,hd,ht,hw,under_append,under_compose]
        rfl

theorem packAux_bound {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) (depth : ℕ) :
    Bounded (packAuxAt length budget current total rest depth).1.2 := by
  induction rest generalizing current total depth with
  | nil => exact block_bound _
  | cons item rest ih =>
      unfold packAuxAt
      dsimp only
      split
      · have h := ih (item::current) (BinaryRationalOpcodeAllocation.applyWithAllocation .add total (length item)).1 (depth+1)
        simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        omega
      · have h := ih [item] (length item) (depth+1)
        simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        omega

def packingAt {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → ℕ → (List (List α × SignedWord) × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),0)
  | item::rest,depth =>
      let later := packAuxAt length budget [item] (length item) rest (depth+1)
      ((later.1.1,.join (.block [.frames (depth+1),.listAllocation 1,.arrayAllocation 8]) later.1.2),later.2)

theorem packing_refines {α : Type*} (length : α → SignedWord) (budget : SignedWord) (items : List α) (depth : ℕ) :
    observe (packingAt length budget items depth) = offset depth (packingWithTraceAndWork length budget items) := by
  cases items with
  | nil => rfl
  | cons item rest =>
      have h := packAux_refines length budget [item] (length item) rest (depth+1)
      simp only [observe,offset,packingAt,packingWithTraceAndWork,denote,data_of_refinement h,
        trace_of_refinement h,work_of_refinement h,under_append,under_compose]
      rfl

theorem packing_bound {α : Type*} (length : α → SignedWord) (budget : SignedWord) (items : List α) (depth : ℕ) :
    Bounded (packingAt length budget items depth).1.2 := by
  cases items with
  | nil => exact block_bound _
  | cons item rest =>
      have h := packAux_bound length budget [item] (length item) rest (depth+1)
      simp only [Bounded,packingAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

def prefixReference {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    ((Classification n × List (List (Fin n) × SignedWord)) × Trace) × ℕ :=
  let result := prefixWithTraceAndArithmeticWork input
  (((result.1.1,result.1.2.1),result.1.2.2),result.2)

def prefixAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    ((Classification n × List (List (Fin n) × SignedWord)) × Plan) × ℕ :=
  let classified := classificationAt input (List.finRange n) (depth+2)
  let packed := packingAt input.length.read input.budget classified.1.1.uniforms (depth+2)
  (((classified.1.1,packed.1.1),.join (.block [.frames (depth+(n+8)),.listAllocation n,.arrayAllocation 8])
    (.join classified.1.2 packed.1.2)),classified.2+packed.2)

theorem prefix_refines {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    observe (prefixAt input depth) = offset depth (prefixReference input) := by
  have hc := classification_refines input (List.finRange n) (depth+2)
  have hp := packing_refines input.length.read input.budget (classificationWithTraceAndWork input (List.finRange n)).1.1.uniforms (depth+2)
  simp only [prefixAt,prefixReference,prefixWithTraceAndArithmeticWork,observe,offset,denote,
    data_of_refinement hc,trace_of_refinement hc,work_of_refinement hc,data_of_refinement hp,
    trace_of_refinement hp,work_of_refinement hp,under_append,under_compose,List.append_nil]
  rfl

theorem prefix_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    Bounded (prefixAt input depth).1.2 := by
  have hc := classification_bound input (List.finRange n) (depth+2)
  have hp := packing_bound input.length.read input.budget (classificationAt input (List.finRange n) (depth+2)).1.1.uniforms (depth+2)
  simp only [Bounded,prefixAt,nodes,payload,List.length_cons,List.length_nil] at hc hp ⊢
  omega

end Blotto.BinaryCachePrefixPlan
