import Blotto.BinaryScalarTape
import Blotto.BinaryPRGHeapFixedProperties
import Blotto.BinaryQuadraticOutputLifetime
import Blotto.BinaryPRGHeaderFrame

/-! Complete prepared physical PRG drawing, original global fallback and actual
quadratic original-budget scaling/coordinate framing. The retained header is
borrowed; original request/precision derive every output-width premise. -/
namespace Blotto.BinaryPRGHeapFramedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGHeapFixedProperties
set_option maxHeartbeats 2000000

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    (List Bool × FixedBinaryWord store.width) × Trace :=
  let drawn := BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar
  let output := BinaryQuadraticOutputLifetime.outputWithTrace request.prepared.original.a header.bytes drawn.1.1
  ((output.1,drawn.1.2),wrap 32 2 [drawn.2,output.2])

theorem runWithTrace_bytes {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    (runWithTrace store request rich K outer scalar header).1.1 =
      BinaryStoredRowFrame.row (BinaryPRGWordControllerRequest.originalFixedSample store request rich K outer scalar) := by
  unfold runWithTrace
  dsimp only
  rw [BinaryQuadraticOutputLifetime.outputWithTrace_erases]
  unfold BinaryQuadraticOutputLifetime.outputData BinaryPRGWordControllerRequest.originalFixedSample BinaryStoredRowFrame.row
  rw [BinaryPRGHeapFixedLifetime.runWithTrace_erasure,header.correct]
  rfl

theorem runWithTrace_cursor {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    (runWithTrace store request rich K outer scalar header).1.2 =
      (BinaryPRGWordControllerRequest.run store request rich K outer scalar).2 :=
  BinaryPRGHeapFixedLifetime.runWithTrace_cursor store request rich K outer scalar

theorem originalFixedSample_canonical {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ∀ j,CanonicalWord ((BinaryPRGWordControllerRequest.originalFixedSample store request rich K outer scalar).read j) := by
  have hNormalized := BinaryPRGWordControllerRequest.fixedSample_canonical store request rich K outer scalar
  have hScale := BinaryQuadraticOutputLifetime.scaleData_state request.prepared.original.a
    (BinaryPRGWordControllerRequest.fixedSample store request rich K outer scalar)
    request.valid.2.1.1.1 (fun j => (hNormalized j).1)
  intro j
  change CanonicalWord ((BinaryQuadraticOutputLifetime.scaleData request.prepared.original.a
    (BinaryPRGWordControllerRequest.fixedSample store request rich K outer scalar)).read j)
  rw [hScale,BinaryPRGOriginalSampler.rescale,FixedArrayTable.read_ofFn]
  exact BinaryPRGRecognition.opcode_canonical .mul _ _ request.valid.2.1.1 (hNormalized j)

theorem runWithTrace_read {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) (suffix : List Bool) :
    BinaryRatListFrame.readRow ((runWithTrace store request rich K outer scalar header).1.1++suffix) =
      some (n,List.ofFn (fun j => value ((BinaryPRGWordControllerRequest.originalFixedSample store request rich K outer scalar).read j)),suffix) := by
  rw [runWithTrace_bytes]
  exact BinaryStoredRowFrame.row_read _ (fun j => (originalFixedSample_canonical store request rich K outer scalar j).1) suffix

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b headerLength : ℕ) : ℕ :=
  BinaryPRGHeapFixedLifetime.envelope request K i b+
    BinaryQuadraticOutputLifetime.bound n (wordWidth request K) headerLength+
    BinaryQuadraticOutputLifetime.frames n (wordWidth request K) headerLength+128

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    usage (runWithTrace store request rich K outer scalar header).2 ≤
      envelope request K store.width store.cap.value header.bytes.length := by
  let drawn := BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar
  let output := BinaryQuadraticOutputLifetime.outputWithTrace request.prepared.original.a header.bytes drawn.1.1
  have hDraw := BinaryPRGHeapFixedLifetime.runWithTrace_usage store request rich K outer scalar
  have hNormalized := BinaryPRGHeapFixedLifetime.runWithTrace_canonical store request rich K outer scalar
  have hOutput := BinaryQuadraticOutputLifetime.outputWithTrace_bounds request.prepared.original.a header.bytes drawn.1.1
    request.valid.2.1.1.1 (fun j => (hNormalized j).1) (wordWidth request K) (scale_width request K)
    (row_width store request rich K outer scalar)
  have hOut : usage output.2 ≤ BinaryQuadraticOutputLifetime.bound n (wordWidth request K) header.bytes.length+
      BinaryQuadraticOutputLifetime.frames n (wordWidth request K) header.bytes.length := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    exact Nat.add_le_add hOutput.1 hOutput.2
  have hw := wrap_usage 32 2 [drawn.2,output.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace store request rich K outer scalar header).2 ≤ _ at hw
  change usage drawn.2 ≤ _ at hDraw
  unfold envelope
  omega

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store request rich K outer scalar header).2 steps ≤
      borrowed+envelope request K store.width store.cap.value header.bytes.length ∧
    framePeak ((runWithTrace store request rich K outer scalar header).2.take steps) ≤
      envelope request K store.width store.cap.value header.bytes.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store request rich K outer scalar header) borrowed steps

end Blotto.BinaryPRGHeapFramedLifetime
