import Blotto.BinaryNormalizationPlan
import Blotto.BinaryPRGPromiseMeasured

/-! Planned delayed guards and structural row/sum control consume actual
planned arithmetic. All preceding data/trace/source records remain exact.
Reached division work is retained; one outer promise emission follows later.
Comparison/primitive/native/physical-space interpretation retains its scope. -/
namespace Blotto.BinaryPromiseControlPlan
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev Record (α : Type*) := ((α × Plan) × ℕ) × ℕ

def Refines {α : Type*} (run : ℕ → Record α) (previous : (α × Trace) × ℕ) : Prop :=
  ∀ depth,view (run depth).1 = offset depth previous

def Safe {α : Type*} (record : Record α) : Prop :=
  Bounded record.1.1.2 ∧ record.2 ≤ 4*record.1.2

def opcodeAt (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) : Record SignedWord :=
  let produced := BinaryNormalizationPlan.applyAt op first second depth
  ((produced.1,produced.2.1),produced.2.2)

theorem opcode_refines (op : RealArithmeticOp) (first second : SignedWord) :
    Refines (opcodeAt op first second) (BinaryQuadraticMeasured.apply op first second) := by
  intro depth
  have h := BinaryNormalizationPlan.apply_refines op first second depth
  simp only [opcodeAt,view,offset,data_refines h,trace_refines h,charge_refines h,BinaryQuadraticMeasured.apply]

theorem opcode_safe (op : RealArithmeticOp) (first second : SignedWord) (depth : ℕ) : Safe (opcodeAt op first second depth) := by
  have hb := BinaryNormalizationPlan.apply_budget op first second depth
  have hc := charge_refines (BinaryNormalizationPlan.apply_refines op first second depth)
  have hd := BinaryQuadraticMeasured.applyMeasured_division_work_bound op first second
  simp only [BinaryQuadraticMeasured.apply] at hd
  simp only [Safe,opcodeAt,hc]
  exact ⟨hb,hd⟩

def comparisonAt (first second : SignedWord) (depth : ℕ) : Record Bool :=
  let compared := BinaryQuadraticExpressionMeasured.compare first second
  (((compared.1.1,.shifted depth compared.1.2),compared.2),0)

theorem comparison_refines (first second : SignedWord) :
    Refines (comparisonAt first second) (BinaryQuadraticExpressionMeasured.compare first second) := by intro depth; rfl

theorem comparison_safe (first second : SignedWord) (depth : ℕ) : Safe (comparisonAt first second depth) := by
  simp [Safe,comparisonAt,Bounded,nodes,payload]

def andThenAt (first : ℕ → Record Bool) (later : Unit → ℕ → Record Bool) (depth : ℕ) : Record Bool :=
  let front := first (depth+2)
  if front.1.1.1 then
    let next := later () (depth+2)
    (((next.1.1.1,.join (.block [.frames (depth+2),.arrayAllocation 16])
      (.join front.1.1.2 next.1.1.2)),front.1.2+next.1.2+4),front.2+next.2)
  else
    (((false,.join (.block [.frames (depth+2),.arrayAllocation 8]) front.1.1.2),front.1.2+4),front.2)

theorem andThen_refines (first : ℕ → Record Bool) (later : Unit → ℕ → Record Bool)
    (oldFirst : (Bool × Trace) × ℕ) (oldLater : Unit → (Bool × Trace) × ℕ)
    (hFirst : Refines first oldFirst) (hLater : ∀ u,Refines (later u) (oldLater u)) :
    Refines (andThenAt first later) (BinaryPRGPromiseControlMeasured.andThen oldFirst oldLater) := by
  intro depth
  have hf := hFirst (depth+2)
  have hl := hLater () (depth+2)
  simp only [andThenAt,BinaryPRGPromiseControlMeasured.andThen,data_refines hf]
  split <;> simp only [view,offset,denote,data_refines hl,trace_refines hf,trace_refines hl,
    charge_refines hf,charge_refines hl,wrap,combine,under_append,under_compose,List.append_nil] <;> rfl

theorem andThen_safe (first : ℕ → Record Bool) (later : Unit → ℕ → Record Bool)
    (hFirst : ∀ depth,Safe (first depth)) (hLater : ∀ u depth,Safe (later u depth)) (depth : ℕ) :
    Safe (andThenAt first later depth) := by
  have hf := hFirst (depth+2)
  have hl := hLater () (depth+2)
  unfold andThenAt
  dsimp only
  split <;> simp only [Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at hf hl ⊢ <;> omega

theorem andThen_reject (first : ℕ → Record Bool) (later : Unit → ℕ → Record Bool) (depth : ℕ)
    (h : (first (depth+2)).1.1.1 = false) :
    andThenAt first later depth =
      (((false,.join (.block [.frames (depth+2),.arrayAllocation 8]) (first (depth+2)).1.1.2),
        (first (depth+2)).1.2+4),(first (depth+2)).2) := by
  simp only [andThenAt,h,Bool.false_eq_true,ite_false]

def positiveAt (word : SignedWord) (depth : ℕ) : Record Bool :=
  let compared := comparisonAt word zero (depth+2)
  (((!compared.1.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8]) compared.1.1.2),compared.1.2+4),compared.2)

theorem positive_refines (word : SignedWord) : Refines (positiveAt word) (BinaryPRGPromiseControlMeasured.positive word) := by
  intro depth
  have h := comparison_refines word zero (depth+2)
  simp only [positiveAt,BinaryPRGPromiseControlMeasured.positive,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem positive_safe (word : SignedWord) (depth : ℕ) : Safe (positiveAt word depth) := by
  have h := comparison_safe word zero (depth+2)
  simp only [positiveAt,Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def equalAt (first second : SignedWord) : ℕ → Record Bool :=
  andThenAt (comparisonAt first second) (fun _ => comparisonAt second first)

theorem equal_refines (first second : SignedWord) : Refines (equalAt first second) (BinaryPRGPromiseControlMeasured.equal first second) :=
  andThen_refines _ _ _ _ (comparison_refines first second) (fun _ => comparison_refines second first)

theorem equal_safe (first second : SignedWord) (depth : ℕ) : Safe (equalAt first second depth) :=
  andThen_safe _ _ (comparison_safe first second) (fun _ => comparison_safe second first) depth

def allAt (produce : SignedWord → ℕ → Record Bool) : List SignedWord → ℕ → Record Bool
  | [],depth => (((true,.block [.frames (depth+1),.arrayAllocation 8]),4),0)
  | word::rest,depth => andThenAt (produce word) (fun _ => allAt produce rest) depth

theorem all_refines (produce : SignedWord → ℕ → Record Bool) (previous : SignedWord → (Bool × Trace) × ℕ)
    (h : ∀ word,Refines (produce word) (previous word)) (words : List SignedWord) :
    Refines (allAt produce words) (BinaryPRGPromiseControlMeasured.all previous words) := by
  induction words with
  | nil => intro depth; rfl
  | cons word rest ih => exact andThen_refines _ _ _ _ (h word) (fun _ => ih)

theorem all_safe (produce : SignedWord → ℕ → Record Bool) (h : ∀ word depth,Safe (produce word depth))
    (words : List SignedWord) (depth : ℕ) : Safe (allAt produce words depth) := by
  induction words generalizing depth with
  | nil => simp [allAt,Safe,Bounded,nodes,payload]
  | cons word rest ih => exact andThen_safe _ _ (h word) (fun _ => ih) depth

def sumAt : List SignedWord → ℕ → Record SignedWord
  | [],depth => (((zero,.block [.frames (depth+1),.arrayAllocation 8]),4),0)
  | word::rest,depth =>
      let tail := sumAt rest (depth+2)
      let head := opcodeAt .add word tail.1.1.1 (depth+2)
      (((head.1.1.1,.join (.block [.frames (depth+2),.arrayAllocation 24])
        (.join tail.1.1.2 head.1.1.2)),tail.1.2+head.1.2+8),tail.2+head.2)

theorem sum_refines (words : List SignedWord) : Refines (sumAt words) (BinaryStoredWordSumMeasured.sum words) := by
  intro depth
  induction words generalizing depth with
  | nil => rfl
  | cons word rest ih =>
      have ht := ih (depth+2)
      have hh := opcode_refines .add word (BinaryStoredWordSumMeasured.sum rest).1.1 (depth+2)
      simp only [sumAt,BinaryStoredWordSumMeasured.sum,view,offset,denote,
        data_refines ht,data_refines hh,trace_refines ht,trace_refines hh,charge_refines ht,charge_refines hh,
        wrap,combine,under_append,under_compose,List.append_nil]
      rfl

theorem sum_safe (words : List SignedWord) (depth : ℕ) : Safe (sumAt words depth) := by
  induction words generalizing depth with
  | nil => simp [sumAt,Safe,Bounded,nodes,payload]
  | cons word rest ih =>
      have ht := ih (depth+2)
      have hh := opcode_safe .add word (sumAt rest (depth+2)).1.1.1 (depth+2)
      simp only [sumAt,Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at ht hh ⊢
      omega

def scaledAt (twice b word : SignedWord) (depth : ℕ) : Record Bool :=
  let scaled := opcodeAt .mul twice word (depth+2)
  let compared := comparisonAt scaled.1.1.1 b (depth+2)
  (((compared.1.1.1,.join (.block [.frames (depth+2),.arrayAllocation 24])
    (.join scaled.1.1.2 compared.1.1.2)),scaled.1.2+compared.1.2+8),scaled.2+compared.2)

theorem scaled_refines (twice b word : SignedWord) :
    Refines (scaledAt twice b word) (BinaryPRGPromiseControlMeasured.scaled twice b word) := by
  intro depth
  have hs := opcode_refines .mul twice word (depth+2)
  have hc := comparison_refines (BinaryQuadraticMeasured.apply .mul twice word).1.1 b (depth+2)
  simp only [scaledAt,BinaryPRGPromiseControlMeasured.scaled,view,offset,denote,
    data_refines hs,data_refines hc,trace_refines hs,trace_refines hc,charge_refines hs,charge_refines hc,
    wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem scaled_safe (twice b word : SignedWord) (depth : ℕ) : Safe (scaledAt twice b word depth) := by
  have hs := opcode_safe .mul twice word (depth+2)
  have hc := comparison_safe (opcodeAt .mul twice word (depth+2)).1.1.1 b (depth+2)
  simp only [scaledAt,Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at hs hc ⊢
  omega

end Blotto.BinaryPromiseControlPlan
