import Blotto.BinaryPromiseOpcodeParser
import Blotto.BinaryRawParserProjection
import Blotto.BinaryNumericalOpcodeRequest

/-! The concrete promise-opcode parser discharges shared-continuation refinement.
Every old full result/source/canonical-parser price remains exact; reached
promise division/planned emission is added without a supplied backend premise. -/
namespace Blotto.BinaryPromiseOpcodeRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Prices := BinaryRawParserContinuation.Prices

def backend : BinaryRawParserContinuation.Backend ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) where
  run := BinaryPromiseOpcodeParser.read
  compat := BinaryPromiseOpcodeParser.read_previous

theorem backend_refines : BinaryRawParserProjection.Refines backend BinaryNumericalOpcodeRequest.backend :=
  BinaryPromiseOpcodeParser.read_compat

set_option cleanup.letToHave false in
def rawWithFactoryExtras (rich : Bool) (frame bits : List Bool) : (((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits

def rawWithControlExtras (rich : Bool) (frame bits : List Bool) : ((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (rawWithFactoryExtras rich frame bits).1

theorem rawWithFactoryExtras_compat (rich : Bool) (frame bits : List Bool) :
    (rawWithFactoryExtras rich frame bits).1 = rawWithControlExtras rich frame bits := rfl

theorem rawWithControlExtras_record (rich : Bool) (frame bits : List Bool) :
    rawWithControlExtras rich frame bits =



  BinaryRawParserContinuation.rawWithControlExtras backend rich frame bits := by
  simp only [rawWithControlExtras,rawWithFactoryExtras,BinaryRawParserContinuation.rawWithFactoryExtras_compat,BinaryRawParserContinuation.parsedRawWithFactoryExtras_compat,BinaryRawParserContinuation.generatedWithFactoryExtras_compat,BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras_compat,BinaryRawParserContinuation.pairWithFactoryExtras_compat,BinaryRawParserContinuation.parsedPairWithFactoryExtras_compat]

def rawWithRouteExtras (rich : Bool) (frame bits : List Bool) : (((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ :=
  (rawWithControlExtras rich frame bits).1

theorem rawWithControlExtras_compat (rich : Bool) (frame bits : List Bool) :
    (rawWithControlExtras rich frame bits).1 = rawWithRouteExtras rich frame bits := rfl

theorem rawWithRouteExtras_record (rich : Bool) (frame bits : List Bool) :
    rawWithRouteExtras rich frame bits =


  BinaryRawParserContinuation.rawWithRouteExtras backend rich frame bits := by
  simp only [rawWithRouteExtras,rawWithControlExtras_record]
  rfl

def rawWithDrawOutputExtras (rich : Bool) (frame bits : List Bool) : ((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ :=
  (rawWithRouteExtras rich frame bits).1

theorem rawWithRouteExtras_compat (rich : Bool) (frame bits : List Bool) :
    (rawWithRouteExtras rich frame bits).1 = rawWithDrawOutputExtras rich frame bits := rfl

theorem rawWithDrawOutputExtras_record (rich : Bool) (frame bits : List Bool) :
    rawWithDrawOutputExtras rich frame bits =

  BinaryRawParserContinuation.rawWithDrawOutputExtras backend rich frame bits := by
  simp only [rawWithDrawOutputExtras,rawWithRouteExtras_record]
  rfl

def rawWithOutputExtras (rich : Bool) (frame bits : List Bool) : (((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ :=
  (rawWithDrawOutputExtras rich frame bits).1

theorem rawWithDrawOutputExtras_compat (rich : Bool) (frame bits : List Bool) :
    (rawWithDrawOutputExtras rich frame bits).1 = rawWithOutputExtras rich frame bits := rfl

theorem rawWithOutputExtras_record (rich : Bool) (frame bits : List Bool) :
    rawWithOutputExtras rich frame bits =
  BinaryRawParserContinuation.rawWithOutputExtras backend rich frame bits := by
  simp only [rawWithOutputExtras,rawWithDrawOutputExtras_record]
  rfl

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))) :=
  (rawWithOutputExtras rich frame bits).1

theorem rawWithOutputExtras_compat (rich : Bool) (frame bits : List Bool) :
    (rawWithOutputExtras rich frame bits).1 = raw rich frame bits := rfl

theorem raw_record (rich : Bool) (frame bits : List Bool) :
    raw rich frame bits =
  BinaryRawParserContinuation.raw backend rich frame bits := by
  rfl


theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryRawParserProjection.keepComplete (raw rich frame bits) = BinaryNumericalOpcodeRequest.raw rich frame bits :=
  BinaryRawParserProjection.raw_keep backend BinaryNumericalOpcodeRequest.backend backend_refines rich frame bits

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (raw_preceding rich frame bits)).trans (BinaryNumericalOpcodeRequest.raw_compat rich frame bits)

set_option cleanup.letToHave false in
def parsedRawWithFactoryExtras (rich : Bool) (frame bits : List Bool) : (((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits

def parsedRawWithControlExtras (rich : Bool) (frame bits : List Bool) : ((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (parsedRawWithFactoryExtras rich frame bits).1

theorem parsedRawWithFactoryExtras_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithFactoryExtras rich frame bits).1 = parsedRawWithControlExtras rich frame bits := rfl

theorem parsedRawWithControlExtras_record (rich : Bool) (frame bits : List Bool) :
    parsedRawWithControlExtras rich frame bits =



  BinaryRawParserContinuation.parsedRawWithControlExtras backend rich frame bits := by
  simp only [parsedRawWithControlExtras,parsedRawWithFactoryExtras,BinaryRawParserContinuation.rawWithFactoryExtras_compat,BinaryRawParserContinuation.parsedRawWithFactoryExtras_compat,BinaryRawParserContinuation.generatedWithFactoryExtras_compat,BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras_compat,BinaryRawParserContinuation.pairWithFactoryExtras_compat,BinaryRawParserContinuation.parsedPairWithFactoryExtras_compat,rawWithFactoryExtras_compat]

def parsedRawWithRouteExtras (rich : Bool) (frame bits : List Bool) : (((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ :=
  (parsedRawWithControlExtras rich frame bits).1

theorem parsedRawWithControlExtras_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithControlExtras rich frame bits).1 = parsedRawWithRouteExtras rich frame bits := rfl

theorem parsedRawWithRouteExtras_record (rich : Bool) (frame bits : List Bool) :
    parsedRawWithRouteExtras rich frame bits =


  BinaryRawParserContinuation.parsedRawWithRouteExtras backend rich frame bits := by
  simp only [parsedRawWithRouteExtras,parsedRawWithControlExtras_record]
  rfl

def parsedRawWithDrawOutputExtras (rich : Bool) (frame bits : List Bool) : ((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ :=
  (parsedRawWithRouteExtras rich frame bits).1

theorem parsedRawWithRouteExtras_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithRouteExtras rich frame bits).1 = parsedRawWithDrawOutputExtras rich frame bits := rfl

theorem parsedRawWithDrawOutputExtras_record (rich : Bool) (frame bits : List Bool) :
    parsedRawWithDrawOutputExtras rich frame bits =

  BinaryRawParserContinuation.parsedRawWithDrawOutputExtras backend rich frame bits := by
  simp only [parsedRawWithDrawOutputExtras,parsedRawWithRouteExtras_record]
  rfl

def parsedRawWithOutputExtras (rich : Bool) (frame bits : List Bool) : (((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ :=
  (parsedRawWithDrawOutputExtras rich frame bits).1

theorem parsedRawWithDrawOutputExtras_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithDrawOutputExtras rich frame bits).1 = parsedRawWithOutputExtras rich frame bits := rfl

theorem parsedRawWithOutputExtras_record (rich : Bool) (frame bits : List Bool) :
    parsedRawWithOutputExtras rich frame bits =
  BinaryRawParserContinuation.parsedRawWithOutputExtras backend rich frame bits := by
  simp only [parsedRawWithOutputExtras,parsedRawWithDrawOutputExtras_record]
  rfl

def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))) :=
  (parsedRawWithOutputExtras rich frame bits).1

theorem parsedRawWithOutputExtras_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithOutputExtras rich frame bits).1 = parsedRaw rich frame bits := rfl

theorem parsedRaw_record (rich : Bool) (frame bits : List Bool) :
    parsedRaw rich frame bits =
  BinaryRawParserContinuation.parsedRaw backend rich frame bits := by
  rfl


theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryRawParserProjection.keepComplete (parsedRaw rich frame bits) = BinaryNumericalOpcodeRequest.parsedRaw rich frame bits :=
  BinaryRawParserProjection.parsedRaw_keep backend BinaryNumericalOpcodeRequest.backend backend_refines rich frame bits

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (parsedRaw_preceding rich frame bits)).trans (BinaryNumericalOpcodeRequest.parsedRaw_compat rich frame bits)

set_option cleanup.letToHave false in
def generatedWithFactoryExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state

def generatedWithControlExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (generatedWithFactoryExtras next rich frame state).1

theorem generatedWithFactoryExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithFactoryExtras next rich frame state).1 = generatedWithControlExtras next rich frame state := rfl

theorem generatedWithControlExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithControlExtras next rich frame state =



  BinaryRawParserContinuation.generatedWithControlExtras backend next rich frame state := by
  simp only [generatedWithControlExtras,generatedWithFactoryExtras,BinaryRawParserContinuation.rawWithFactoryExtras_compat,BinaryRawParserContinuation.parsedRawWithFactoryExtras_compat,BinaryRawParserContinuation.generatedWithFactoryExtras_compat,BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras_compat,BinaryRawParserContinuation.pairWithFactoryExtras_compat,BinaryRawParserContinuation.parsedPairWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat]

def generatedWithRouteExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ :=
  (generatedWithControlExtras next rich frame state).1

theorem generatedWithControlExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithControlExtras next rich frame state).1 = generatedWithRouteExtras next rich frame state := rfl

theorem generatedWithRouteExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithRouteExtras next rich frame state =


  BinaryRawParserContinuation.generatedWithRouteExtras backend next rich frame state := by
  simp only [generatedWithRouteExtras,generatedWithControlExtras_record]
  rfl

def generatedWithDrawOutputExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ :=
  (generatedWithRouteExtras next rich frame state).1

theorem generatedWithRouteExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithRouteExtras next rich frame state).1 = generatedWithDrawOutputExtras next rich frame state := rfl

theorem generatedWithDrawOutputExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithDrawOutputExtras next rich frame state =

  BinaryRawParserContinuation.generatedWithDrawOutputExtras backend next rich frame state := by
  simp only [generatedWithDrawOutputExtras,generatedWithRouteExtras_record]
  rfl

def generatedWithOutputExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ :=
  (generatedWithDrawOutputExtras next rich frame state).1

theorem generatedWithDrawOutputExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithDrawOutputExtras next rich frame state).1 = generatedWithOutputExtras next rich frame state := rfl

theorem generatedWithOutputExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithOutputExtras next rich frame state =
  BinaryRawParserContinuation.generatedWithOutputExtras backend next rich frame state := by
  simp only [generatedWithOutputExtras,generatedWithDrawOutputExtras_record]
  rfl

def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))) :=
  (generatedWithOutputExtras next rich frame state).1

theorem generatedWithOutputExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithOutputExtras next rich frame state).1 = generated next rich frame state := rfl

theorem generated_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generated next rich frame state =
  BinaryRawParserContinuation.generated backend next rich frame state := by
  rfl


theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (generated next rich frame state) = BinaryNumericalOpcodeRequest.generated next rich frame state :=
  BinaryRawParserProjection.generated_keep backend BinaryNumericalOpcodeRequest.backend backend_refines next rich frame state

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (generated_preceding next rich frame state)).trans (BinaryNumericalOpcodeRequest.generated_compat next rich frame state)

set_option cleanup.letToHave false in
def parsedGeneratedWithFactoryExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state

def parsedGeneratedWithControlExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (parsedGeneratedWithFactoryExtras next rich frame state).1

theorem parsedGeneratedWithFactoryExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithFactoryExtras next rich frame state).1 = parsedGeneratedWithControlExtras next rich frame state := rfl

theorem parsedGeneratedWithControlExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithControlExtras next rich frame state =



  BinaryRawParserContinuation.parsedGeneratedWithControlExtras backend next rich frame state := by
  simp only [parsedGeneratedWithControlExtras,parsedGeneratedWithFactoryExtras,BinaryRawParserContinuation.rawWithFactoryExtras_compat,BinaryRawParserContinuation.parsedRawWithFactoryExtras_compat,BinaryRawParserContinuation.generatedWithFactoryExtras_compat,BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras_compat,BinaryRawParserContinuation.pairWithFactoryExtras_compat,BinaryRawParserContinuation.parsedPairWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat,generatedWithFactoryExtras_compat]

def parsedGeneratedWithRouteExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ :=
  (parsedGeneratedWithControlExtras next rich frame state).1

theorem parsedGeneratedWithControlExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithControlExtras next rich frame state).1 = parsedGeneratedWithRouteExtras next rich frame state := rfl

theorem parsedGeneratedWithRouteExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithRouteExtras next rich frame state =


  BinaryRawParserContinuation.parsedGeneratedWithRouteExtras backend next rich frame state := by
  simp only [parsedGeneratedWithRouteExtras,parsedGeneratedWithControlExtras_record]
  rfl

def parsedGeneratedWithDrawOutputExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ :=
  (parsedGeneratedWithRouteExtras next rich frame state).1

theorem parsedGeneratedWithRouteExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithRouteExtras next rich frame state).1 = parsedGeneratedWithDrawOutputExtras next rich frame state := rfl

theorem parsedGeneratedWithDrawOutputExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithDrawOutputExtras next rich frame state =

  BinaryRawParserContinuation.parsedGeneratedWithDrawOutputExtras backend next rich frame state := by
  simp only [parsedGeneratedWithDrawOutputExtras,parsedGeneratedWithRouteExtras_record]
  rfl

def parsedGeneratedWithOutputExtras {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ :=
  (parsedGeneratedWithDrawOutputExtras next rich frame state).1

theorem parsedGeneratedWithDrawOutputExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithDrawOutputExtras next rich frame state).1 = parsedGeneratedWithOutputExtras next rich frame state := rfl

theorem parsedGeneratedWithOutputExtras_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithOutputExtras next rich frame state =
  BinaryRawParserContinuation.parsedGeneratedWithOutputExtras backend next rich frame state := by
  simp only [parsedGeneratedWithOutputExtras,parsedGeneratedWithDrawOutputExtras_record]
  rfl

def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))) :=
  (parsedGeneratedWithOutputExtras next rich frame state).1

theorem parsedGeneratedWithOutputExtras_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithOutputExtras next rich frame state).1 = parsedGenerated next rich frame state := rfl

theorem parsedGenerated_record {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGenerated next rich frame state =
  BinaryRawParserContinuation.parsedGenerated backend next rich frame state := by
  rfl


theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (parsedGenerated next rich frame state) = BinaryNumericalOpcodeRequest.parsedGenerated next rich frame state :=
  BinaryRawParserProjection.parsedGenerated_keep backend BinaryNumericalOpcodeRequest.backend backend_refines next rich frame state

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (parsedGenerated_preceding next rich frame state)).trans (BinaryNumericalOpcodeRequest.parsedGenerated_compat next rich frame state)

set_option cleanup.letToHave false in
def pairWithFactoryExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state

def pairWithControlExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (pairWithFactoryExtras next frame state).1

theorem pairWithFactoryExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithFactoryExtras next frame state).1 = pairWithControlExtras next frame state := rfl

theorem pairWithControlExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithControlExtras next frame state =



  BinaryRawParserContinuation.pairWithControlExtras backend next frame state := by
  simp only [pairWithControlExtras,pairWithFactoryExtras,BinaryRawParserContinuation.rawWithFactoryExtras_compat,BinaryRawParserContinuation.parsedRawWithFactoryExtras_compat,BinaryRawParserContinuation.generatedWithFactoryExtras_compat,BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras_compat,BinaryRawParserContinuation.pairWithFactoryExtras_compat,BinaryRawParserContinuation.parsedPairWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat,generatedWithFactoryExtras_compat,parsedGeneratedWithFactoryExtras_compat]

def pairWithRouteExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ :=
  (pairWithControlExtras next frame state).1

theorem pairWithControlExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithControlExtras next frame state).1 = pairWithRouteExtras next frame state := rfl

theorem pairWithRouteExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithRouteExtras next frame state =


  BinaryRawParserContinuation.pairWithRouteExtras backend next frame state := by
  simp only [pairWithRouteExtras,pairWithControlExtras_record]
  rfl

def pairWithDrawOutputExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ :=
  (pairWithRouteExtras next frame state).1

theorem pairWithRouteExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithRouteExtras next frame state).1 = pairWithDrawOutputExtras next frame state := rfl

theorem pairWithDrawOutputExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithDrawOutputExtras next frame state =

  BinaryRawParserContinuation.pairWithDrawOutputExtras backend next frame state := by
  simp only [pairWithDrawOutputExtras,pairWithRouteExtras_record]
  rfl

def pairWithOutputExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ :=
  (pairWithDrawOutputExtras next frame state).1

theorem pairWithDrawOutputExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithDrawOutputExtras next frame state).1 = pairWithOutputExtras next frame state := rfl

theorem pairWithOutputExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithOutputExtras next frame state =
  BinaryRawParserContinuation.pairWithOutputExtras backend next frame state := by
  simp only [pairWithOutputExtras,pairWithDrawOutputExtras_record]
  rfl

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))) :=
  (pairWithOutputExtras next frame state).1

theorem pairWithOutputExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithOutputExtras next frame state).1 = pair next frame state := rfl

theorem pair_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pair next frame state =
  BinaryRawParserContinuation.pair backend next frame state := by
  rfl


theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (pair next frame state) = BinaryNumericalOpcodeRequest.pair next frame state :=
  BinaryRawParserProjection.pair_keep backend BinaryNumericalOpcodeRequest.backend backend_refines next frame state

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (pair_preceding next frame state)).trans (BinaryNumericalOpcodeRequest.pair_compat next frame state)

set_option cleanup.letToHave false in
def parsedPairWithFactoryExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state

def parsedPairWithControlExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (parsedPairWithFactoryExtras next frame state).1

theorem parsedPairWithFactoryExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithFactoryExtras next frame state).1 = parsedPairWithControlExtras next frame state := rfl

theorem parsedPairWithControlExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithControlExtras next frame state =



  BinaryRawParserContinuation.parsedPairWithControlExtras backend next frame state := by
  simp only [parsedPairWithControlExtras,parsedPairWithFactoryExtras,BinaryRawParserContinuation.rawWithFactoryExtras_compat,BinaryRawParserContinuation.parsedRawWithFactoryExtras_compat,BinaryRawParserContinuation.generatedWithFactoryExtras_compat,BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras_compat,BinaryRawParserContinuation.pairWithFactoryExtras_compat,BinaryRawParserContinuation.parsedPairWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat,generatedWithFactoryExtras_compat,parsedGeneratedWithFactoryExtras_compat,pairWithFactoryExtras_compat]

def parsedPairWithRouteExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ :=
  (parsedPairWithControlExtras next frame state).1

theorem parsedPairWithControlExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithControlExtras next frame state).1 = parsedPairWithRouteExtras next frame state := rfl

theorem parsedPairWithRouteExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithRouteExtras next frame state =


  BinaryRawParserContinuation.parsedPairWithRouteExtras backend next frame state := by
  simp only [parsedPairWithRouteExtras,parsedPairWithControlExtras_record]
  rfl

def parsedPairWithDrawOutputExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ :=
  (parsedPairWithRouteExtras next frame state).1

theorem parsedPairWithRouteExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithRouteExtras next frame state).1 = parsedPairWithDrawOutputExtras next frame state := rfl

theorem parsedPairWithDrawOutputExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithDrawOutputExtras next frame state =

  BinaryRawParserContinuation.parsedPairWithDrawOutputExtras backend next frame state := by
  simp only [parsedPairWithDrawOutputExtras,parsedPairWithRouteExtras_record]
  rfl

def parsedPairWithOutputExtras {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ :=
  (parsedPairWithDrawOutputExtras next frame state).1

theorem parsedPairWithDrawOutputExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithDrawOutputExtras next frame state).1 = parsedPairWithOutputExtras next frame state := rfl

theorem parsedPairWithOutputExtras_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithOutputExtras next frame state =
  BinaryRawParserContinuation.parsedPairWithOutputExtras backend next frame state := by
  simp only [parsedPairWithOutputExtras,parsedPairWithDrawOutputExtras_record]
  rfl

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))) :=
  (parsedPairWithOutputExtras next frame state).1

theorem parsedPairWithOutputExtras_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithOutputExtras next frame state).1 = parsedPair next frame state := rfl

theorem parsedPair_record {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPair next frame state =
  BinaryRawParserContinuation.parsedPair backend next frame state := by
  rfl


theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryRawParserProjection.keepComplete (parsedPair next frame state) = BinaryNumericalOpcodeRequest.parsedPair next frame state :=
  BinaryRawParserProjection.parsedPair_keep backend BinaryNumericalOpcodeRequest.backend backend_refines next frame state

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (parsedPair_preceding next frame state)).trans (BinaryNumericalOpcodeRequest.parsedPair_compat next frame state)

end Blotto.BinaryPromiseOpcodeRequest
