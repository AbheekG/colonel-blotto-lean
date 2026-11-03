import Blotto.BinaryAllPayloadParser
import Blotto.BinaryRawParserContinuation

/-! The concrete all-payload parser discharges shared-continuation refinement.
Every old full result/source/canonical-parser price remains exact; reached
dimension/accuracy payload emission is added without a supplied backend premise. -/
namespace Blotto.BinaryAllPayloadRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Prices := BinaryRawParserContinuation.Prices

def backend : BinaryRawParserContinuation.Backend ℕ where
  run := BinaryAllPayloadParser.read
  compat := BinaryAllPayloadParser.read_previous

theorem backend_refines : BinaryRawParserContinuation.Refines backend := BinaryAllPayloadParser.read_compat

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryRawParserContinuation.raw backend rich frame bits

theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (raw rich frame bits) = BinaryParserPayloadRequest.raw rich frame bits :=
  BinaryRawParserContinuation.raw_preceding backend backend_refines rich frame bits

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (raw_preceding rich frame bits)).trans (BinaryParserPayloadRequest.raw_compat rich frame bits)

def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryRawParserContinuation.parsedRaw backend rich frame bits

theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (parsedRaw rich frame bits) = BinaryParserPayloadRequest.parsedRaw rich frame bits :=
  BinaryRawParserContinuation.parsedRaw_preceding backend backend_refines rich frame bits

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (parsedRaw_preceding rich frame bits)).trans (BinaryParserPayloadRequest.parsedRaw_compat rich frame bits)

def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryRawParserContinuation.generated backend next rich frame state

theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (generated next rich frame state) = BinaryParserPayloadRequest.generated next rich frame state :=
  BinaryRawParserContinuation.generated_preceding backend backend_refines next rich frame state

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (generated_preceding next rich frame state)).trans (BinaryParserPayloadRequest.generated_compat next rich frame state)

def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryRawParserContinuation.parsedGenerated backend next rich frame state

theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedGenerated next rich frame state) = BinaryParserPayloadRequest.parsedGenerated next rich frame state :=
  BinaryRawParserContinuation.parsedGenerated_preceding backend backend_refines next rich frame state

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (parsedGenerated_preceding next rich frame state)).trans (BinaryParserPayloadRequest.parsedGenerated_compat next rich frame state)

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryRawParserContinuation.pair backend next frame state

theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (pair next frame state) = BinaryParserPayloadRequest.pair next frame state :=
  BinaryRawParserContinuation.pair_preceding backend backend_refines next frame state

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (pair_preceding next frame state)).trans (BinaryParserPayloadRequest.pair_compat next frame state)

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  BinaryRawParserContinuation.parsedPair backend next frame state

theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedPair next frame state) = BinaryParserPayloadRequest.parsedPair next frame state :=
  BinaryRawParserContinuation.parsedPair_preceding backend backend_refines next frame state

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (parsedPair_preceding next frame state)).trans (BinaryParserPayloadRequest.parsedPair_compat next frame state)

end Blotto.BinaryAllPayloadRequest
