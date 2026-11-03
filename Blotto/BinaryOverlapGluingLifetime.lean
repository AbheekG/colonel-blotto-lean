import Blotto.BinaryFourGluingParentsLifetime
import Blotto.BinaryOverlapCompilerBridge

/-! One traced sixteen-word environment per selected pair feeds the actual
weight and eight endpoint programs. A retained slot table is then projected
into the three arrays required by the 81-slot overlap descriptor. -/
namespace Blotto.BinaryOverlapGluingLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryStoredOverlapEnvironment BinarySyntaxUniformWork
set_option maxHeartbeats 4000000

def environmentWithTrace {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : FixedArrayTable 16 SignedWord × Trace :=
  (environment first second interval budget i j,wrap 64 2 [])

theorem environmentWithTrace_usage {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    usage (environmentWithTrace first second interval budget i j).2 ≤ 66 := by
  have hw := wrap_usage 64 2 []
  change usage (wrap 64 2 []) ≤ _
  simpa only [List.map_nil,List.sum_nil,Nat.add_zero] using hw

def slotWithTrace {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    (SignedWord × FixedArrayTable 4 SignedWord × FixedArrayTable 4 SignedWord) × Trace :=
  let env := environmentWithTrace first second interval budget i j
  let weight := BinaryQuadraticSyntaxLifetime.runWithTrace env.1 BinaryOverlapCompilerBridge.weight
  let P := BinaryLifetimeArray.build 4 (fun r => BinaryQuadraticSyntaxLifetime.runWithTrace env.1 (BinaryOverlapCompilerBridge.safeP r))
  let Q := BinaryLifetimeArray.build 4 (fun r => BinaryQuadraticSyntaxLifetime.runWithTrace env.1 (BinaryOverlapCompilerBridge.safeQ r))
  ((weight.1,P.1,Q.1),wrap 64 4 [env.2,weight.2,P.2,Q.2])

theorem slotWithTrace_erasure {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h)
    (hFirst : first.Canonical) (hSecond : second.Canonical)
    (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget) :
    (slotWithTrace first second interval budget i j).1 =
      let env := environment first second interval budget i j
      (((BinaryOverlapCompilerBridge.weight).compile.run env).1,
        FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeP r).compile.run env).1),
        FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeQ r).compile.run env).1)) := by
  unfold slotWithTrace environmentWithTrace
  dsimp only
  simp only [BinaryLifetimeArray.build_erases,
    BinaryQuadraticSyntaxLifetime.runWithTrace_state _ _
      (environment_canonical first second interval budget i j hFirst hSecond hInterval hBudget)]

def descriptorWithTrace {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) : Segment 4 (k * h) × Trace :=
  let slots := BinaryLifetimeArray.build (k * h) (fun slot =>
    let pair := finProdFinEquiv.symm slot
    slotWithTrace first second interval budget pair.1 pair.2)
  let weight := BinaryLifetimeArray.build (k * h) (fun slot => ((slots.1.read slot).1,wrap 4 1 []))
  let P := BinaryLifetimeArray.build (k * h) (fun slot => ((slots.1.read slot).2.1,wrap 4 1 []))
  let Q := BinaryLifetimeArray.build (k * h) (fun slot => ((slots.1.read slot).2.2,wrap 4 1 []))
  (⟨weight.1,P.1,Q.1⟩,wrap 64 4 [slots.2,weight.2,P.2,Q.2])

theorem descriptorWithTrace_erasure {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (hFirst : first.Canonical) (hSecond : second.Canonical)
    (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget) :
    (descriptorWithTrace first second interval budget).1 = compileDescriptor first second interval budget := by
  simp only [descriptorWithTrace,compileDescriptor,BinaryLifetimeArray.build_erases,
    FixedArrayTable.read_ofFn,slotWithTrace_erasure first second interval budget _ _ hFirst hSecond hInterval hBudget]

theorem weight_sizes :
    BinaryOverlapCompilerBridge.weight.rational.depth ≤ 16 ∧
    BinaryOverlapCompilerBridge.weight.rational.operationBound ≤ 256 ∧
    BinaryOverlapCompilerBridge.weight.nodes ≤ 256 := by decide

theorem safeP_sizes (r : Fin 4) :
    (BinaryOverlapCompilerBridge.safeP r).rational.depth ≤ 16 ∧
    (BinaryOverlapCompilerBridge.safeP r).rational.operationBound ≤ 256 ∧
    (BinaryOverlapCompilerBridge.safeP r).nodes ≤ 256 := by fin_cases r <;> decide

theorem safeQ_sizes (r : Fin 4) :
    (BinaryOverlapCompilerBridge.safeQ r).rational.depth ≤ 16 ∧
    (BinaryOverlapCompilerBridge.safeQ r).rational.operationBound ≤ 256 ∧
    (BinaryOverlapCompilerBridge.safeQ r).nodes ≤ 256 := by fin_cases r <;> decide

def expressionBound (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.bound 256 256 s 16
def expressionFrames (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.frames 256 s 16
def slotEnvelope (s : ℕ) : ℕ := 9 * (expressionBound s + expressionFrames s) + 512
def copyEnvelope (n : ℕ) : ℕ := 5 * n + 2 * (n + 1)^2 + 15
def descriptorEnvelope (n s : ℕ) : ℕ :=
  n * slotEnvelope s + slotEnvelope s + 2 * (n + 1)^2 + n + 14 + 3 * copyEnvelope n + 96

theorem slotWithTrace_usage {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h)
    (hFirst : first.Canonical) (hSecond : second.Canonical)
    (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s)
    (hHeight : EnvHeight (environment first second interval budget i j) s) :
    usage (slotWithTrace first second interval budget i j).2 ≤ slotEnvelope s := by
  let env := environmentWithTrace first second interval budget i j
  let weight := BinaryQuadraticSyntaxLifetime.runWithTrace env.1 BinaryOverlapCompilerBridge.weight
  let P := BinaryLifetimeArray.build 4 (fun r =>
    BinaryQuadraticSyntaxLifetime.runWithTrace env.1 (BinaryOverlapCompilerBridge.safeP r))
  let Q := BinaryLifetimeArray.build 4 (fun r =>
    BinaryQuadraticSyntaxLifetime.runWithTrace env.1 (BinaryOverlapCompilerBridge.safeQ r))
  have hC := environment_canonical first second interval budget i j hFirst hSecond hInterval hBudget
  have hWeight := BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env.1 BinaryOverlapCompilerBridge.weight
    hC s 16 256 256 hs hHeight weight_sizes.1 weight_sizes.2.1 weight_sizes.2.2
  have hP := fun r => BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env.1 (BinaryOverlapCompilerBridge.safeP r)
    hC s 16 256 256 hs hHeight (safeP_sizes r).1 (safeP_sizes r).2.1 (safeP_sizes r).2.2
  have hQ := fun r => BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env.1 (BinaryOverlapCompilerBridge.safeQ r)
    hC s 16 256 256 hs hHeight (safeQ_sizes r).1 (safeQ_sizes r).2.1 (safeQ_sizes r).2.2
  have hp := array_usage 4 (fun r => BinaryQuadraticSyntaxLifetime.runWithTrace env.1 (BinaryOverlapCompilerBridge.safeP r))
    (expressionBound s) (expressionFrames s) (fun r => (hP r).1) (fun r => (hP r).2)
  have hq := array_usage 4 (fun r => BinaryQuadraticSyntaxLifetime.runWithTrace env.1 (BinaryOverlapCompilerBridge.safeQ r))
    (expressionBound s) (expressionFrames s) (fun r => (hQ r).1) (fun r => (hQ r).2)
  have he := environmentWithTrace_usage first second interval budget i j
  have hw := wrap_usage 64 4 [env.2,weight.2,P.2,Q.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage env.2 ≤ _ at he
  have hWeightCells : listCells weight.2 + arraySlots weight.2 ≤ expressionBound s := hWeight.1
  have hWeightFrames : framePeak weight.2 ≤ expressionFrames s := hWeight.2
  have hWeightUsage : usage weight.2 ≤ expressionBound s + expressionFrames s := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  change usage P.2 ≤ _ at hp
  change usage Q.2 ≤ _ at hq
  change usage (wrap 64 4 [env.2,weight.2,P.2,Q.2]) ≤ _
  unfold slotEnvelope
  omega

theorem descriptorWithTrace_usage {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (hFirst : first.Canonical) (hSecond : second.Canonical)
    (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s)
    (hHeight : ∀ i j,EnvHeight (environment first second interval budget i j) s) :
    usage (descriptorWithTrace first second interval budget).2 ≤ descriptorEnvelope (k * h) s := by
  let n := k * h
  let slots := BinaryLifetimeArray.build n (fun slot =>
    let pair := finProdFinEquiv.symm slot
    slotWithTrace first second interval budget pair.1 pair.2)
  let weight := BinaryLifetimeArray.build n (fun slot => ((slots.1.read slot).1,wrap 4 1 []))
  let P := BinaryLifetimeArray.build n (fun slot => ((slots.1.read slot).2.1,wrap 4 1 []))
  let Q := BinaryLifetimeArray.build n (fun slot => ((slots.1.read slot).2.2,wrap 4 1 []))
  have hEach : ∀ slot : Fin n,usage (slotWithTrace first second interval budget
      (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2).2 ≤ slotEnvelope s := by
    intro slot
    exact slotWithTrace_usage first second interval budget _ _ hFirst hSecond hInterval hBudget s hs (hHeight _ _)
  have hSlots := array_usage n (fun slot =>
    let pair := finProdFinEquiv.symm slot
    slotWithTrace first second interval budget pair.1 pair.2)
    (slotEnvelope s) (slotEnvelope s)
    (by intro slot; have he := hEach slot; dsimp only at he ⊢; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at he; omega)
    (by intro slot; have he := hEach slot; dsimp only at he ⊢; unfold usage at he; omega)
  have hCopyCells : listCells (wrap 4 1 []) + arraySlots (wrap 4 1 []) ≤ 4 := by
    simp [wrap,combine,listCells,arraySlots]
  have hCopyFrames : framePeak (wrap 4 1 []) ≤ 1 := by
    simp [wrap,combine,framePeak]
  have hWeight := array_usage n (fun slot => ((slots.1.read slot).1,wrap 4 1 [])) 4 1
    (fun _ => hCopyCells) (fun _ => hCopyFrames)
  have hP := array_usage n (fun slot => ((slots.1.read slot).2.1,wrap 4 1 [])) 4 1
    (fun _ => hCopyCells) (fun _ => hCopyFrames)
  have hQ := array_usage n (fun slot => ((slots.1.read slot).2.2,wrap 4 1 [])) 4 1
    (fun _ => hCopyCells) (fun _ => hCopyFrames)
  have hw := wrap_usage 64 4 [slots.2,weight.2,P.2,Q.2]
  simp only [List.map_cons,List.map_nil,List.sum_nil,List.sum_cons] at hw
  change usage slots.2 ≤ _ at hSlots
  change usage weight.2 ≤ _ at hWeight
  change usage P.2 ≤ _ at hP
  change usage Q.2 ≤ _ at hQ
  change usage (wrap 64 4 [slots.2,weight.2,P.2,Q.2]) ≤ _
  dsimp only [n] at hSlots hWeight hP hQ hw ⊢
  unfold descriptorEnvelope copyEnvelope
  omega

theorem all_prefix {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (hFirst : first.Canonical) (hSecond : second.Canonical)
    (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s)
    (hHeight : ∀ i j,EnvHeight (environment first second interval budget i j) s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptorWithTrace first second interval budget).2 steps ≤
        borrowed + descriptorEnvelope (k * h) s ∧
      framePeak ((descriptorWithTrace first second interval budget).2.take steps) ≤ descriptorEnvelope (k * h) s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (descriptorWithTrace_usage first second interval budget hFirst hSecond hInterval hBudget s hs hHeight) borrowed steps

end Blotto.BinaryOverlapGluingLifetime
