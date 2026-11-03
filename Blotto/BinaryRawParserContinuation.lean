import Blotto.BinaryParserPayloadRequest

/-! One reusable raw continuation consumes an actual physical parser and
preserves the whole preceding parser/source/canonical-emission record. Parser
compatibility/refinement fields are erased; concrete producers discharge them. -/
namespace Blotto.BinaryRawParserContinuation
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Prices := BinaryParserPayloadRequest.Prices × ℕ

structure Backend (E : Type*) where
  run : (frame : List Bool) →
    ((((Option Parsed × Trace) × ℕ) × ℕ) × E)
  compat : ∀ frame,(run frame).1.1 = BinaryPRGPhysicalRawRequestMeasured.read frame

def Refines {E : Type*} (backend : Backend E) : Prop :=
  ∀ frame,(backend.run frame).1 = BinaryPhysicalPayloadPlan.read frame

theorem read_original {E : Type*} (backend : Backend E) (frame : List Bool) :
    (backend.run frame).1.1.1 = BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame :=
  (congrArg Prod.fst (backend.compat frame)).trans (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)

variable {E : Type*} [Zero E] [Add E]

set_option cleanup.letToHave false in
def rawWithFactoryExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : (((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let factoryReturned := BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hOriginal rich bits
        let controlled := factoryReturned.1
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        ((((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2),factoryReturned.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)

def rawWithControlExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : ((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (rawWithFactoryExtras backend rich frame bits).1

theorem rawWithFactoryExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (rawWithFactoryExtras backend rich frame bits).1 = rawWithControlExtras backend rich frame bits := rfl

theorem rawWithControlExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    rawWithControlExtras backend rich frame bits =



  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (((((result,((0,0),((0,price),produced.2))),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let controlled := BinaryCacheFinishRequest.seedWithControlExtras frame parsed hOriginal rich bits
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (((((result,((0,0),((0,price),produced.2))),0),0),0),0) := by
  simp only [rawWithControlExtras,rawWithFactoryExtras,BinaryCacheFinishRequest.seedWithFactoryExtras_compat]
  split <;> first | rfl | (split <;> rfl)

def rawWithRouteExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : (((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ :=
  (rawWithControlExtras backend rich frame bits).1

theorem rawWithControlExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (rawWithControlExtras backend rich frame bits).1 = rawWithRouteExtras backend rich frame bits := rfl

theorem rawWithRouteExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    rawWithRouteExtras backend rich frame bits =


  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      ((((result,((0,0),((0,price),produced.2))),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let all := BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hOriginal rich bits
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        ((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        ((((result,((0,0),((0,price),produced.2))),0),0),0) := by
  simp only [rawWithRouteExtras,rawWithControlExtras_record]
  split
  · rfl
  · split <;> rfl

def rawWithDrawOutputExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : ((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ :=
  (rawWithRouteExtras backend rich frame bits).1

theorem rawWithRouteExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (rawWithRouteExtras backend rich frame bits).1 = rawWithDrawOutputExtras backend rich frame bits := rfl

theorem rawWithDrawOutputExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    rawWithDrawOutputExtras backend rich frame bits =

  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (((result,((0,0),((0,price),produced.2))),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let collected := BinaryCacheFinishRequest.seedWithDrawOutputExtras frame parsed hOriginal rich bits
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (((result,((0,0),((0,price),produced.2))),0),0) := by
  simp only [rawWithDrawOutputExtras,rawWithRouteExtras_record]
  split
  · rfl
  · split <;> rfl

def rawWithOutputExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : (((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ :=
  (rawWithDrawOutputExtras backend rich frame bits).1

theorem rawWithDrawOutputExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (rawWithDrawOutputExtras backend rich frame bits).1 = rawWithOutputExtras backend rich frame bits := rfl

theorem rawWithOutputExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    rawWithOutputExtras backend rich frame bits =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      ((result,((0,0),((0,price),produced.2))),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let sampled := BinaryCacheFinishRequest.seedWithOutputExtras frame parsed hOriginal rich bits
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        ((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        ((result,((0,0),((0,price),produced.2))),0) := by
  simp only [rawWithOutputExtras,rawWithDrawOutputExtras_record]
  split
  · rfl
  · split <;> rfl

def raw (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E)) :=
  (rawWithOutputExtras backend rich frame bits).1

theorem rawWithOutputExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (rawWithOutputExtras backend rich frame bits).1 = raw backend rich frame bits := rfl

theorem raw_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    raw backend rich frame bits =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,((0,0),((0,price),produced.2)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich bits
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (result,(child.2.1,((child.2.2,price),produced.2)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (result,((0,0),((0,price),produced.2))) := by
  simp only [raw,rawWithOutputExtras_record]
  split
  · rfl
  · split <;> simp only [BinaryCacheFinishRequest.seedWithOutputExtras_compat]


set_option cleanup.letToHave false in
def parsedRawWithFactoryExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : (((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let factoryReturned := BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hOriginal rich bits
        let controlled := factoryReturned.1
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        ((((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2),factoryReturned.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)

def parsedRawWithControlExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : ((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (parsedRawWithFactoryExtras backend rich frame bits).1

theorem parsedRawWithFactoryExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithFactoryExtras backend rich frame bits).1 = parsedRawWithControlExtras backend rich frame bits := rfl

theorem parsedRawWithControlExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    parsedRawWithControlExtras backend rich frame bits =



  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (((((result,((0,0),((0,price),produced.2))),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let controlled := BinaryCacheFinishRequest.seedWithControlExtras frame parsed hOriginal rich bits
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (((((result,((0,0),((0,price),produced.2))),0),0),0),0) := by
  simp only [parsedRawWithControlExtras,parsedRawWithFactoryExtras,BinaryCacheFinishRequest.seedWithFactoryExtras_compat,rawWithFactoryExtras_compat]
  split <;> first | rfl | (split <;> rfl)

def parsedRawWithRouteExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : (((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ :=
  (parsedRawWithControlExtras backend rich frame bits).1

theorem parsedRawWithControlExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithControlExtras backend rich frame bits).1 = parsedRawWithRouteExtras backend rich frame bits := rfl

theorem parsedRawWithRouteExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    parsedRawWithRouteExtras backend rich frame bits =


  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      ((((result,((0,0),((0,price),produced.2))),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let all := BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hOriginal rich bits
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        ((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        ((((result,((0,0),((0,price),produced.2))),0),0),0) := by
  simp only [parsedRawWithRouteExtras,parsedRawWithControlExtras_record]
  split
  · rfl
  · split <;> rfl

def parsedRawWithDrawOutputExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : ((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ :=
  (parsedRawWithRouteExtras backend rich frame bits).1

theorem parsedRawWithRouteExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithRouteExtras backend rich frame bits).1 = parsedRawWithDrawOutputExtras backend rich frame bits := rfl

theorem parsedRawWithDrawOutputExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    parsedRawWithDrawOutputExtras backend rich frame bits =

  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (((result,((0,0),((0,price),produced.2))),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let collected := BinaryCacheFinishRequest.seedWithDrawOutputExtras frame parsed hOriginal rich bits
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (((result,((0,0),((0,price),produced.2))),0),0) := by
  simp only [parsedRawWithDrawOutputExtras,parsedRawWithRouteExtras_record]
  split
  · rfl
  · split <;> rfl

def parsedRawWithOutputExtras (backend : Backend E) (rich : Bool) (frame bits : List Bool) : (((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ :=
  (parsedRawWithDrawOutputExtras backend rich frame bits).1

theorem parsedRawWithDrawOutputExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithDrawOutputExtras backend rich frame bits).1 = parsedRawWithOutputExtras backend rich frame bits := rfl

theorem parsedRawWithOutputExtras_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    parsedRawWithOutputExtras backend rich frame bits =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      ((result,((0,0),((0,price),produced.2))),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let sampled := BinaryCacheFinishRequest.seedWithOutputExtras frame parsed hOriginal rich bits
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        ((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        ((result,((0,0),((0,price),produced.2))),0) := by
  simp only [parsedRawWithOutputExtras,parsedRawWithDrawOutputExtras_record]
  split
  · rfl
  · split <;> rfl

def parsedRaw (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E)) :=
  (parsedRawWithOutputExtras backend rich frame bits).1

theorem parsedRawWithOutputExtras_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRawWithOutputExtras backend rich frame bits).1 = parsedRaw backend rich frame bits := rfl

theorem parsedRaw_record (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    parsedRaw backend rich frame bits =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,((0,0),((0,price),produced.2)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich bits
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (result,(child.2.1,((child.2.2,price),produced.2)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (result,((0,0),((0,price),produced.2))) := by
  simp only [parsedRaw,parsedRawWithOutputExtras_record]
  split
  · rfl
  · split <;> simp only [BinaryCacheFinishRequest.seedWithOutputExtras_compat]


set_option cleanup.letToHave false in
def generatedWithFactoryExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let factoryReturned := BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hOriginal rich generated.1.1.1
        let controlled := factoryReturned.1
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        ((((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2),factoryReturned.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)

def generatedWithControlExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (generatedWithFactoryExtras backend next rich frame state).1

theorem generatedWithFactoryExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithFactoryExtras backend next rich frame state).1 = generatedWithControlExtras backend next rich frame state := rfl

theorem generatedWithControlExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithControlExtras backend next rich frame state =



  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (((((result,((0,0),((0,price),produced.2))),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let controlled := BinaryCacheFinishRequest.seedWithControlExtras frame parsed hOriginal rich generated.1.1.1
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (((((result,((0,0),((0,price),produced.2))),0),0),0),0) := by
  simp only [generatedWithControlExtras,generatedWithFactoryExtras,BinaryCacheFinishRequest.seedWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat]
  split <;> first | rfl | (split <;> rfl)

def generatedWithRouteExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ :=
  (generatedWithControlExtras backend next rich frame state).1

theorem generatedWithControlExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithControlExtras backend next rich frame state).1 = generatedWithRouteExtras backend next rich frame state := rfl

theorem generatedWithRouteExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithRouteExtras backend next rich frame state =


  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      ((((result,((0,0),((0,price),produced.2))),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let all := BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hOriginal rich generated.1.1.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        ((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        ((((result,((0,0),((0,price),produced.2))),0),0),0) := by
  simp only [generatedWithRouteExtras,generatedWithControlExtras_record]
  split
  · rfl
  · split <;> rfl

def generatedWithDrawOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ :=
  (generatedWithRouteExtras backend next rich frame state).1

theorem generatedWithRouteExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithRouteExtras backend next rich frame state).1 = generatedWithDrawOutputExtras backend next rich frame state := rfl

theorem generatedWithDrawOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithDrawOutputExtras backend next rich frame state =

  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (((result,((0,0),((0,price),produced.2))),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let collected := BinaryCacheFinishRequest.seedWithDrawOutputExtras frame parsed hOriginal rich generated.1.1.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (((result,((0,0),((0,price),produced.2))),0),0) := by
  simp only [generatedWithDrawOutputExtras,generatedWithRouteExtras_record]
  split
  · rfl
  · split <;> rfl

def generatedWithOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ :=
  (generatedWithDrawOutputExtras backend next rich frame state).1

theorem generatedWithDrawOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithDrawOutputExtras backend next rich frame state).1 = generatedWithOutputExtras backend next rich frame state := rfl

theorem generatedWithOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generatedWithOutputExtras backend next rich frame state =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      ((result,((0,0),((0,price),produced.2))),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let sampled := BinaryCacheFinishRequest.seedWithOutputExtras frame parsed hOriginal rich generated.1.1.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        ((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        ((result,((0,0),((0,price),produced.2))),0) := by
  simp only [generatedWithOutputExtras,generatedWithDrawOutputExtras_record]
  split
  · rfl
  · split <;> rfl

def generated (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E)) :=
  (generatedWithOutputExtras backend next rich frame state).1

theorem generatedWithOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generatedWithOutputExtras backend next rich frame state).1 = generated backend next rich frame state := rfl

theorem generated_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    generated backend next rich frame state =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,((0,0),((0,price),produced.2)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich generated.1.1.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (result,(child.2.1,((child.2.2,price),produced.2)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (result,((0,0),((0,price),produced.2))) := by
  simp only [generated,generatedWithOutputExtras_record]
  split
  · rfl
  · split <;> simp only [BinaryCacheFinishRequest.seedWithOutputExtras_compat]


set_option cleanup.letToHave false in
def parsedGeneratedWithFactoryExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let factoryReturned := BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hOriginal rich generated.1.1.1
        let controlled := factoryReturned.1
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        ((((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2),factoryReturned.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        ((((((result,((0,0),((0,price),produced.2))),0),0),0),0),0)

def parsedGeneratedWithControlExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (parsedGeneratedWithFactoryExtras backend next rich frame state).1

theorem parsedGeneratedWithFactoryExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithFactoryExtras backend next rich frame state).1 = parsedGeneratedWithControlExtras backend next rich frame state := rfl

theorem parsedGeneratedWithControlExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithControlExtras backend next rich frame state =



  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (((((result,((0,0),((0,price),produced.2))),0),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let controlled := BinaryCacheFinishRequest.seedWithControlExtras frame parsed hOriginal rich generated.1.1.1
        let all := controlled.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2),controlled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (((((result,((0,0),((0,price),produced.2))),0),0),0),0) := by
  simp only [parsedGeneratedWithControlExtras,parsedGeneratedWithFactoryExtras,BinaryCacheFinishRequest.seedWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat,generatedWithFactoryExtras_compat]
  split <;> first | rfl | (split <;> rfl)

def parsedGeneratedWithRouteExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ :=
  (parsedGeneratedWithControlExtras backend next rich frame state).1

theorem parsedGeneratedWithControlExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithControlExtras backend next rich frame state).1 = parsedGeneratedWithRouteExtras backend next rich frame state := rfl

theorem parsedGeneratedWithRouteExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithRouteExtras backend next rich frame state =


  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      ((((result,((0,0),((0,price),produced.2))),0),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let all := BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hOriginal rich generated.1.1.1
        let collected := all.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        ((((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2),all.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        ((((result,((0,0),((0,price),produced.2))),0),0),0) := by
  simp only [parsedGeneratedWithRouteExtras,parsedGeneratedWithControlExtras_record]
  split
  · rfl
  · split <;> rfl

def parsedGeneratedWithDrawOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ :=
  (parsedGeneratedWithRouteExtras backend next rich frame state).1

theorem parsedGeneratedWithRouteExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithRouteExtras backend next rich frame state).1 = parsedGeneratedWithDrawOutputExtras backend next rich frame state := rfl

theorem parsedGeneratedWithDrawOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithDrawOutputExtras backend next rich frame state =

  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (((result,((0,0),((0,price),produced.2))),0),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let collected := BinaryCacheFinishRequest.seedWithDrawOutputExtras frame parsed hOriginal rich generated.1.1.1
        let sampled := collected.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2),collected.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (((result,((0,0),((0,price),produced.2))),0),0) := by
  simp only [parsedGeneratedWithDrawOutputExtras,parsedGeneratedWithRouteExtras_record]
  split
  · rfl
  · split <;> rfl

def parsedGeneratedWithOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ :=
  (parsedGeneratedWithDrawOutputExtras backend next rich frame state).1

theorem parsedGeneratedWithDrawOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithDrawOutputExtras backend next rich frame state).1 = parsedGeneratedWithOutputExtras backend next rich frame state := rfl

theorem parsedGeneratedWithOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGeneratedWithOutputExtras backend next rich frame state =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      ((result,((0,0),((0,price),produced.2))),0)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let sampled := BinaryCacheFinishRequest.seedWithOutputExtras frame parsed hOriginal rich generated.1.1.1
        let child := sampled.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        ((result,(child.2.1,((child.2.2,price),produced.2))),sampled.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        ((result,((0,0),((0,price),produced.2))),0) := by
  simp only [parsedGeneratedWithOutputExtras,parsedGeneratedWithDrawOutputExtras_record]
  split
  · rfl
  · split <;> rfl

def parsedGenerated (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E)) :=
  (parsedGeneratedWithOutputExtras backend next rich frame state).1

theorem parsedGeneratedWithOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGeneratedWithOutputExtras backend next rich frame state).1 = parsedGenerated backend next rich frame state := rfl

theorem parsedGenerated_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    parsedGenerated backend next rich frame state =
  let produced := backend.run frame
  let decoded := produced.1.1
  let price := produced.1.1.2+produced.1.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,((0,0),((0,price),produced.2)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (read_original backend frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich generated.1.1.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (result,(child.2.1,((child.2.2,price),produced.2)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (result,((0,0),((0,price),produced.2))) := by
  simp only [parsedGenerated,parsedGeneratedWithOutputExtras_record]
  split
  · rfl
  · split <;> simp only [BinaryCacheFinishRequest.seedWithOutputExtras_compat]


theorem raw_preceding (backend : Backend E) (hRun : Refines backend) (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (raw backend rich frame bits) = BinaryParserPayloadRequest.raw rich frame bits := by
  have hRecord := hRun frame
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  rw [raw_record]
  unfold BinaryParserPayloadRequest.raw BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical]

theorem parsedRaw_preceding (backend : Backend E) (hRun : Refines backend) (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (parsedRaw backend rich frame bits) = BinaryParserPayloadRequest.parsedRaw rich frame bits := by
  have hRecord := hRun frame
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  rw [parsedRaw_record]
  unfold BinaryParserPayloadRequest.parsedRaw BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical]

theorem generated_preceding (backend : Backend E) (hRun : Refines backend) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (generated backend next rich frame state) = BinaryParserPayloadRequest.generated next rich frame state := by
  have hRecord := hRun frame
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  rw [generated_record]
  unfold BinaryParserPayloadRequest.generated BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical]

theorem parsedGenerated_preceding (backend : Backend E) (hRun : Refines backend) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedGenerated backend next rich frame state) = BinaryParserPayloadRequest.parsedGenerated next rich frame state := by
  have hRecord := hRun frame
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  rw [parsedGenerated_record]
  unfold BinaryParserPayloadRequest.parsedGenerated BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical]

set_option cleanup.letToHave false in
def pairWithFactoryExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let firstFactory := generatedWithFactoryExtras backend next true frame state
  let firstControlled := firstFactory.1
  let firstAll := firstControlled.1
  let firstCollected := firstAll.1
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondFactory := generatedWithFactoryExtras backend next false frame rich.1.1.1.1.2
  let secondControlled := secondFactory.1
  let secondAll := secondControlled.1
  let secondCollected := secondAll.1
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  ((((((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2),firstAll.2+secondAll.2),firstControlled.2+secondControlled.2),firstFactory.2+secondFactory.2)

def pairWithControlExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (pairWithFactoryExtras backend next frame state).1

theorem pairWithFactoryExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithFactoryExtras backend next frame state).1 = pairWithControlExtras backend next frame state := rfl

theorem pairWithControlExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithControlExtras backend next frame state =



  let firstControlled := generatedWithControlExtras backend next true frame state
  let firstAll := firstControlled.1
  let firstCollected := firstAll.1
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondControlled := generatedWithControlExtras backend next false frame rich.1.1.1.1.2
  let secondAll := secondControlled.1
  let secondCollected := secondAll.1
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (((((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2),firstAll.2+secondAll.2),firstControlled.2+secondControlled.2) := by
  simp only [pairWithControlExtras,pairWithFactoryExtras,BinaryCacheFinishRequest.seedWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat,generatedWithFactoryExtras_compat,parsedGeneratedWithFactoryExtras_compat]

def pairWithRouteExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ :=
  (pairWithControlExtras backend next frame state).1

theorem pairWithControlExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithControlExtras backend next frame state).1 = pairWithRouteExtras backend next frame state := rfl

theorem pairWithRouteExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithRouteExtras backend next frame state =


  let firstAll := generatedWithRouteExtras backend next true frame state
  let firstCollected := firstAll.1
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondAll := generatedWithRouteExtras backend next false frame rich.1.1.1.1.2
  let secondCollected := secondAll.1
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  ((((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2),firstAll.2+secondAll.2) := by
  simp only [pairWithRouteExtras,pairWithControlExtras_record]
  rfl

def pairWithDrawOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ :=
  (pairWithRouteExtras backend next frame state).1

theorem pairWithRouteExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithRouteExtras backend next frame state).1 = pairWithDrawOutputExtras backend next frame state := rfl

theorem pairWithDrawOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithDrawOutputExtras backend next frame state =

  let firstCollected := generatedWithDrawOutputExtras backend next true frame state
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondCollected := generatedWithDrawOutputExtras backend next false frame rich.1.1.1.1.2
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2) := by
  simp only [pairWithDrawOutputExtras,pairWithRouteExtras_record]
  rfl

def pairWithOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ :=
  (pairWithDrawOutputExtras backend next frame state).1

theorem pairWithDrawOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithDrawOutputExtras backend next frame state).1 = pairWithOutputExtras backend next frame state := rfl

theorem pairWithOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithOutputExtras backend next frame state =
  let firstProduced := generatedWithOutputExtras backend next true frame state
  let first := firstProduced.1
  let rich := first.1
  let secondProduced := generatedWithOutputExtras backend next false frame rich.1.1.1.1.2
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  ((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2) := by
  simp only [pairWithOutputExtras,pairWithDrawOutputExtras_record]
  rfl

def pair (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E)) :=
  (pairWithOutputExtras backend next frame state).1

theorem pairWithOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithOutputExtras backend next frame state).1 = pair backend next frame state := rfl

theorem pair_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pair backend next frame state =
  let first := generated backend next true frame state
  let rich := first.1
  let second := generated backend next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)) := by
  simp only [pair,pairWithOutputExtras_record,generatedWithOutputExtras_compat]


set_option cleanup.letToHave false in
def parsedPairWithFactoryExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let firstFactory := parsedGeneratedWithFactoryExtras backend next true frame state
  let firstControlled := firstFactory.1
  let firstAll := firstControlled.1
  let firstCollected := firstAll.1
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondFactory := parsedGeneratedWithFactoryExtras backend next false frame rich.1.1.1.1.2
  let secondControlled := secondFactory.1
  let secondAll := secondControlled.1
  let secondCollected := secondAll.1
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  ((((((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2),firstAll.2+secondAll.2),firstControlled.2+secondControlled.2),firstFactory.2+secondFactory.2)

def parsedPairWithControlExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ) × ℕ :=
  (parsedPairWithFactoryExtras backend next frame state).1

theorem parsedPairWithFactoryExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithFactoryExtras backend next frame state).1 = parsedPairWithControlExtras backend next frame state := rfl

theorem parsedPairWithControlExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithControlExtras backend next frame state =



  let firstControlled := parsedGeneratedWithControlExtras backend next true frame state
  let firstAll := firstControlled.1
  let firstCollected := firstAll.1
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondControlled := parsedGeneratedWithControlExtras backend next false frame rich.1.1.1.1.2
  let secondAll := secondControlled.1
  let secondCollected := secondAll.1
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (((((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2),firstAll.2+secondAll.2),firstControlled.2+secondControlled.2) := by
  simp only [parsedPairWithControlExtras,parsedPairWithFactoryExtras,BinaryCacheFinishRequest.seedWithFactoryExtras_compat,rawWithFactoryExtras_compat,parsedRawWithFactoryExtras_compat,generatedWithFactoryExtras_compat,parsedGeneratedWithFactoryExtras_compat,pairWithFactoryExtras_compat]

def parsedPairWithRouteExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ) × ℕ :=
  (parsedPairWithControlExtras backend next frame state).1

theorem parsedPairWithControlExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithControlExtras backend next frame state).1 = parsedPairWithRouteExtras backend next frame state := rfl

theorem parsedPairWithRouteExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithRouteExtras backend next frame state =


  let firstAll := parsedGeneratedWithRouteExtras backend next true frame state
  let firstCollected := firstAll.1
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondAll := parsedGeneratedWithRouteExtras backend next false frame rich.1.1.1.1.2
  let secondCollected := secondAll.1
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  ((((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2),firstAll.2+secondAll.2) := by
  simp only [parsedPairWithRouteExtras,parsedPairWithControlExtras_record]
  rfl

def parsedPairWithDrawOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : ((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ) × ℕ :=
  (parsedPairWithRouteExtras backend next frame state).1

theorem parsedPairWithRouteExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithRouteExtras backend next frame state).1 = parsedPairWithDrawOutputExtras backend next frame state := rfl

theorem parsedPairWithDrawOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithDrawOutputExtras backend next frame state =

  let firstCollected := parsedGeneratedWithDrawOutputExtras backend next true frame state
  let firstProduced := firstCollected.1
  let first := firstProduced.1
  let rich := first.1
  let secondCollected := parsedGeneratedWithDrawOutputExtras backend next false frame rich.1.1.1.1.2
  let secondProduced := secondCollected.1
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2),firstCollected.2+secondCollected.2) := by
  simp only [parsedPairWithDrawOutputExtras,parsedPairWithRouteExtras_record]
  rfl

def parsedPairWithOutputExtras (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) : (((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E))) × ℕ :=
  (parsedPairWithDrawOutputExtras backend next frame state).1

theorem parsedPairWithDrawOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithDrawOutputExtras backend next frame state).1 = parsedPairWithOutputExtras backend next frame state := rfl

theorem parsedPairWithOutputExtras_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPairWithOutputExtras backend next frame state =
  let firstProduced := parsedGeneratedWithOutputExtras backend next true frame state
  let first := firstProduced.1
  let rich := first.1
  let secondProduced := parsedGeneratedWithOutputExtras backend next false frame rich.1.1.1.1.2
  let second := secondProduced.1
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  ((result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)),firstProduced.2+secondProduced.2) := by
  simp only [parsedPairWithOutputExtras,parsedPairWithDrawOutputExtras_record]
  rfl

def parsedPair (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × E)) :=
  (parsedPairWithOutputExtras backend next frame state).1

theorem parsedPairWithOutputExtras_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPairWithOutputExtras backend next frame state).1 = parsedPair backend next frame state := rfl

theorem parsedPair_record (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    parsedPair backend next frame state =
  let first := parsedGenerated backend next true frame state
  let rich := first.1
  let second := parsedGenerated backend next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)) := by
  simp only [parsedPair,parsedPairWithOutputExtras_record,parsedGeneratedWithOutputExtras_compat]


theorem pair_preceding (backend : Backend E) (hRun : Refines backend)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (pair backend next frame state) = BinaryParserPayloadRequest.pair next frame state := by
  change BinaryCacheContinuationProjection.keepComplete (pair backend next frame state) =
    (
      let first := BinaryParserPayloadRequest.generated next true frame state
      let rich := first.1
      let second := BinaryParserPayloadRequest.generated next false frame rich.1.1.1.1.2
      let poor := second.1
      let result :=
        let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
        let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
        ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
          BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
      (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)))
  simp only [pair_record,← generated_preceding backend hRun,BinaryCacheContinuationProjection.keepComplete]
  rfl

theorem parsedPair_preceding (backend : Backend E) (hRun : Refines backend)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedPair backend next frame state) = BinaryParserPayloadRequest.parsedPair next frame state := by
  change BinaryCacheContinuationProjection.keepComplete (parsedPair backend next frame state) =
    (
      let first := BinaryParserPayloadRequest.parsedGenerated next true frame state
      let rich := first.1
      let second := BinaryParserPayloadRequest.parsedGenerated next false frame rich.1.1.1.1.2
      let poor := second.1
      let result :=
        let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
        let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
        ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
          BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
      (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)))
  simp only [parsedPair_record,← parsedGenerated_preceding backend hRun,BinaryCacheContinuationProjection.keepComplete]
  rfl

end Blotto.BinaryRawParserContinuation
