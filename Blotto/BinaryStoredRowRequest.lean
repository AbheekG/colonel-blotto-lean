import Blotto.BinaryStoredRowParser
import Blotto.BinaryRawParserProjection
import Blotto.BinaryHeaderControlRequest

/-! The concrete stored-row parser discharges shared-continuation refinement.
Every old full result/source/canonical-parser price remains exact; reached
row emission is added without a supplied backend premise. -/
namespace Blotto.BinaryStoredRowRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Prices := BinaryRawParserContinuation.Prices

def backend : BinaryRawParserContinuation.Backend (((ℕ × ℕ) × ℕ) × ℕ) where
  run := BinaryStoredRowParser.read
  compat := BinaryStoredRowParser.read_previous

theorem backend_refines : BinaryRawParserProjection.Refines backend BinaryHeaderControlRequest.backend :=
  BinaryStoredRowParser.read_compat

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × (((ℕ × ℕ) × ℕ) × ℕ))) :=
  BinaryRawParserContinuation.raw backend rich frame bits

theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryRawParserProjection.keepComplete (raw rich frame bits) = BinaryHeaderControlRequest.raw rich frame bits :=
  BinaryRawParserProjection.raw_keep backend BinaryHeaderControlRequest.backend backend_refines rich frame bits

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (raw_preceding rich frame bits)).trans (BinaryHeaderControlRequest.raw_compat rich frame bits)

def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × (((ℕ × ℕ) × ℕ) × ℕ))) :=
  BinaryRawParserContinuation.parsedRaw backend rich frame bits

theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryRawParserProjection.keepComplete (parsedRaw rich frame bits) = BinaryHeaderControlRequest.parsedRaw rich frame bits :=
  BinaryRawParserProjection.parsedRaw_keep backend BinaryHeaderControlRequest.backend backend_refines rich frame bits

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (parsedRaw_preceding rich frame bits)).trans (BinaryHeaderControlRequest.parsedRaw_compat rich frame bits)

def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × (((ℕ × ℕ) × ℕ) × ℕ))) :=
  BinaryRawParserContinuation.generated backend next rich frame state

theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (generated next rich frame state) = BinaryHeaderControlRequest.generated next rich frame state :=
  BinaryRawParserProjection.generated_keep backend BinaryHeaderControlRequest.backend backend_refines next rich frame state

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (generated_preceding next rich frame state)).trans (BinaryHeaderControlRequest.generated_compat next rich frame state)

def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × (((ℕ × ℕ) × ℕ) × ℕ))) :=
  BinaryRawParserContinuation.parsedGenerated backend next rich frame state

theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (parsedGenerated next rich frame state) = BinaryHeaderControlRequest.parsedGenerated next rich frame state :=
  BinaryRawParserProjection.parsedGenerated_keep backend BinaryHeaderControlRequest.backend backend_refines next rich frame state

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (parsedGenerated_preceding next rich frame state)).trans (BinaryHeaderControlRequest.parsedGenerated_compat next rich frame state)

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × (((ℕ × ℕ) × ℕ) × ℕ))) :=
  BinaryRawParserContinuation.pair backend next frame state

theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (pair next frame state) = BinaryHeaderControlRequest.pair next frame state :=
  BinaryRawParserProjection.pair_keep backend BinaryHeaderControlRequest.backend backend_refines next frame state

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (pair_preceding next frame state)).trans (BinaryHeaderControlRequest.pair_compat next frame state)

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × (((ℕ × ℕ) × ℕ) × ℕ))) :=
  BinaryRawParserContinuation.parsedPair backend next frame state

theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (parsedPair next frame state) = BinaryHeaderControlRequest.parsedPair next frame state :=
  BinaryRawParserProjection.parsedPair_keep backend BinaryHeaderControlRequest.backend backend_refines next frame state

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (parsedPair_preceding next frame state)).trans (BinaryHeaderControlRequest.parsedPair_compat next frame state)

end Blotto.BinaryStoredRowRequest
