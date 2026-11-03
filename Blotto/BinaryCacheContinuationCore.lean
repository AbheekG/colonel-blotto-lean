import Blotto.BinaryPhysicalCachePlan
import Blotto.BinaryCacheEmissionBounds
import Blotto.BinaryInitializerEmissionBounds

/-! The shared continuation starts at an actual complete cache producer with a full
preceding-record refinement. Extra prices retain their own type and flow through
all reached children and sequential pairs. Concrete backends must be instantiated
and bounded before this is a complete execution theorem. -/
namespace Blotto.BinaryCacheContinuationCore
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryTerminalCacheCertificate
set_option autoImplicit false
set_option maxHeartbeats 3000000


structure Backend (E : Type*) where
  run : (parsed : PhysicalRequest) → (seed : BinarySeedLookupTree.Store) → (rich : Bool) →
    (((((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) ×
      BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)
  compat : ∀ parsed seed rich, (run parsed seed rich).1 = BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich

variable {E : Type*} [Zero E] [Add E]

def certified (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let child := backend.run parsed.1 seed rich
  let returned := child.1
  let result :=
    let observed := returned.1
    match hs : observed.1.1.1.1 with
    | none =>
        let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
        (((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
    | some result =>
        let certified := certifyWithTrace result.2
          (BinaryTerminalPhysicalAllowanceCertified.cache_correct frame parsed hParsed seed rich result
            (by simpa only [observed,returned,child,backend.compat,BinaryTerminalPhysicalAllowanceCache.run] using hs))
        let emitted := BinaryWrapperEmission.two 24 2 observed.1.2 certified.2
        (((((some ⟨result.1,certified.1⟩,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (result,child.2)

theorem certified_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified backend frame parsed hParsed seed rich).1 = BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich := by
  have hData := congrArg (fun produced => produced.1.1.1.1.1) (backend.compat parsed.1 seed rich)
  unfold certified BinaryTerminalPhysicalAllowanceCertified.runWithCharges
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [backend.compat]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      simp only [backend.compat]


set_option cleanup.letToHave false in
def drawWithFactoryExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : (((((((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ) × ℕ :=
  let request := parsed.1.2.logical.request
  let child := certified backend frame parsed hParsed seed rich
  let returned := child.1
  let completed :=
    let observed := returned.1
    match hs : observed.1.1.1.1 with
    | none =>
        let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
        (((((((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),0),0),0),0)
    | some result =>
        let factoryReturned := BinaryWordTerminalCompleteMeasured.runWithFactoryExtras seed result.2
          (terminal_canonical request rich result.1)
          (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
            (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
              (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs)))
          K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
            (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
        let controlled := factoryReturned.1
        let all := controlled.1
        let actual := all.1
        let drawn := actual.1
        let emitted := BinaryWrapperEmission.two 32 2 observed.1.2 drawn.1.2
        ((((((((drawn.1.1,observed.1.1.2),emitted.1),observed.2+drawn.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),actual.2),all.2),controlled.2),factoryReturned.2)
  let retainedCompleted := completed.1
  (((((retainedCompleted.1.1.1,child.2),retainedCompleted.1.1.2),retainedCompleted.1.2),retainedCompleted.2),completed.2)

def drawWithControlExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : ((((((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ :=
  (drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem drawWithFactoryExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1 = drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar := rfl

theorem drawWithControlExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar =



  let request := parsed.1.2.logical.request
  let child := certified backend frame parsed hParsed seed rich
  let returned := child.1
  let completed :=
    let observed := returned.1
    match hs : observed.1.1.1.1 with
    | none =>
        let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
        ((((((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),0),0),0)
    | some result =>
        let controlled := BinaryWordTerminalCompleteMeasured.runWithControlExtras seed result.2
          (terminal_canonical request rich result.1)
          (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
            (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
              (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs)))
          K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
            (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
        let all := controlled.1
        let actual := all.1
        let drawn := actual.1
        let emitted := BinaryWrapperEmission.two 32 2 observed.1.2 drawn.1.2
        (((((((drawn.1.1,observed.1.1.2),emitted.1),observed.2+drawn.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),actual.2),all.2),controlled.2)
  ((((completed.1.1.1,child.2),completed.1.1.2),completed.1.2),completed.2) := by
  simp only [drawWithControlExtras,drawWithFactoryExtras,BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.runWithFactoryExtras_compat]
  split <;> first | rfl | (split <;> rfl)

def drawWithRouteExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : (((((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ :=
  (drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem drawWithControlExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1 = drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar := rfl

theorem drawWithRouteExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar =


  let request := parsed.1.2.logical.request
  let child := certified backend frame parsed hParsed seed rich
  let returned := child.1
  let completed :=
    let observed := returned.1
    match hs : observed.1.1.1.1 with
    | none =>
        let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
        (((((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),0),0)
    | some result =>
        let all := BinaryWordTerminalCompleteMeasured.runWithRouteExtras seed result.2
          (terminal_canonical request rich result.1)
          (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
            (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
              (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs)))
          K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
            (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
        let actual := all.1
        let drawn := actual.1
        let emitted := BinaryWrapperEmission.two 32 2 observed.1.2 drawn.1.2
        ((((((drawn.1.1,observed.1.1.2),emitted.1),observed.2+drawn.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),actual.2),all.2)
  (((completed.1.1,child.2),completed.1.2),completed.2) := by
  simp only [drawWithRouteExtras,drawWithControlExtras_record]
  split <;> rfl

def drawWithDrawExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : ((((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ :=
  (drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem drawWithRouteExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1 = drawWithDrawExtras backend frame parsed hParsed seed rich K outer scalar := rfl

theorem drawWithDrawExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    drawWithDrawExtras backend frame parsed hParsed seed rich K outer scalar =

  let request := parsed.1.2.logical.request
  let child := certified backend frame parsed hParsed seed rich
  let returned := child.1
  let completed :=
    let observed := returned.1
    match hs : observed.1.1.1.1 with
    | none =>
        let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
        ((((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),0)
    | some result =>
        let actual := BinaryWordTerminalCompleteMeasured.runWithDrawExtras seed result.2
          (terminal_canonical request rich result.1)
          (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
            (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
              (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs)))
          K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
            (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
        let drawn := actual.1
        let emitted := BinaryWrapperEmission.two 32 2 observed.1.2 drawn.1.2
        (((((drawn.1.1,observed.1.1.2),emitted.1),observed.2+drawn.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2),actual.2)
  ((completed.1,child.2),completed.2) := by
  simp only [drawWithDrawExtras,drawWithRouteExtras_record]
  split <;> rfl

def draw (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  (drawWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem drawWithDrawExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (drawWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).1 = draw backend frame parsed hParsed seed rich K outer scalar := rfl

theorem draw_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    draw backend frame parsed hParsed seed rich K outer scalar =
  let request := parsed.1.2.logical.request
  let child := certified backend frame parsed hParsed seed rich
  let returned := child.1
  let result :=
    let observed := returned.1
    match hs : observed.1.1.1.1 with
    | none =>
        let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
        (((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
    | some result =>
        let drawn := BinaryWordTerminalCompleteMeasured.run seed result.2
          (terminal_canonical request rich result.1)
          (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
            (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
              (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs)))
          K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
            (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
        let emitted := BinaryWrapperEmission.two 32 2 observed.1.2 drawn.1.2
        ((((drawn.1.1,observed.1.1.2),emitted.1),observed.2+drawn.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (result,child.2) := by
  simp only [draw,drawWithDrawExtras_record]
  split <;> rfl

theorem draw_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw backend frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar := by
  have hData := congrArg (fun produced => produced.1.1.1.1.1) (certified_compat backend frame parsed hParsed seed rich)
  simp only [draw_record,BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges]
  split
  · rename_i hNone
    split
    · simp only [certified_compat]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      simp only [certified_compat]


set_option cleanup.letToHave false in
def fixedWithFactoryExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : ((((((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ) × ℕ :=
  let factoryReturned := drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar
  let controlled := factoryReturned.1
  let all := controlled.1
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let result :=
    let drawn := returned.1
    match drawn.1.1.1.1 with
    | some row =>
        let emitted := BinaryWrapperEmission.one 24 2 drawn.1.2
        (((((row,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
    | none =>
        let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
        let emitted := BinaryWrapperEmission.two 32 2 drawn.1.2 fallback.1.2
        (((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+fallback.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (((((result,child.2),supplied.2),all.2),controlled.2),factoryReturned.2)

def fixedWithControlExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : (((((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ :=
  (fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem fixedWithFactoryExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1 = fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar := rfl

theorem fixedWithControlExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar =



  let controlled := drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar
  let all := controlled.1
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let result :=
    let drawn := returned.1
    match drawn.1.1.1.1 with
    | some row =>
        let emitted := BinaryWrapperEmission.one 24 2 drawn.1.2
        (((((row,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
    | none =>
        let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
        let emitted := BinaryWrapperEmission.two 32 2 drawn.1.2 fallback.1.2
        (((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+fallback.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  ((((result,child.2),supplied.2),all.2),controlled.2) := by
  simp only [fixedWithControlExtras,fixedWithFactoryExtras,BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.runWithFactoryExtras_compat,drawWithFactoryExtras_compat]

def fixedWithRouteExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : ((((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ :=
  (fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem fixedWithControlExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1 = fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar := rfl

theorem fixedWithRouteExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar =


  let all := drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let result :=
    let drawn := returned.1
    match drawn.1.1.1.1 with
    | some row =>
        let emitted := BinaryWrapperEmission.one 24 2 drawn.1.2
        (((((row,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
    | none =>
        let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
        let emitted := BinaryWrapperEmission.two 32 2 drawn.1.2 fallback.1.2
        (((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+fallback.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (((result,child.2),supplied.2),all.2) := by
  simp only [fixedWithRouteExtras,fixedWithControlExtras_record]
  rfl

def fixedWithDrawExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) : (((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ :=
  (fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem fixedWithRouteExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1 = fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar := rfl

theorem fixedWithDrawExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar =

  let supplied := drawWithDrawExtras backend frame parsed hParsed seed rich K outer scalar
  let child := supplied.1
  let returned := child.1
  let result :=
    let drawn := returned.1
    match drawn.1.1.1.1 with
    | some row =>
        let emitted := BinaryWrapperEmission.one 24 2 drawn.1.2
        (((((row,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
    | none =>
        let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
        let emitted := BinaryWrapperEmission.two 32 2 drawn.1.2 fallback.1.2
        (((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+fallback.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  ((result,child.2),supplied.2) := by
  simp only [fixedWithDrawExtras,fixedWithRouteExtras_record]
  rfl

def fixed (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  (fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).1

theorem fixedWithDrawExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar).1 = fixed backend frame parsed hParsed seed rich K outer scalar := rfl

theorem fixed_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    fixed backend frame parsed hParsed seed rich K outer scalar =
  let child := draw backend frame parsed hParsed seed rich K outer scalar
  let returned := child.1
  let result :=
    let drawn := returned.1
    match drawn.1.1.1.1 with
    | some row =>
        let emitted := BinaryWrapperEmission.one 24 2 drawn.1.2
        (((((row,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+4),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
    | none =>
        let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
        let emitted := BinaryWrapperEmission.two 32 2 drawn.1.2 fallback.1.2
        (((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+fallback.2+8),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (result,child.2) := by
  simp only [fixed,fixedWithDrawExtras_record]
  rfl

theorem fixed_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed backend frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar := by
  have hData := congrArg (fun produced => produced.1.1.1.1.1) (draw_compat backend frame parsed hParsed seed rich K outer scalar)
  simp only [fixed_record,BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges]
  split
  · rename_i row hSome
    split
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      simp only [draw_compat]
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
  · rename_i hNone
    split
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
    · simp only [draw_compat]


set_option cleanup.letToHave false in
def framedWithFactoryExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : (((((((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let factoryReturned := fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar
  let controlled := factoryReturned.1
  let all := controlled.1
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  let produced := BinaryPhysicalOutputMeasured.outputWithExtras parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList
  let output := produced.1
  let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
  let result :=
    (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
      BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  ((((((result,child.2),produced.2),supplied.2),all.2),controlled.2),factoryReturned.2)

def framedWithControlExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : ((((((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ) × ℕ :=
  (framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1

theorem framedWithFactoryExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1 = framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header := rfl

theorem framedWithControlExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header =



  let controlled := fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar
  let all := controlled.1
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  let produced := BinaryPhysicalOutputMeasured.outputWithExtras parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList
  let output := produced.1
  let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
  let result :=
    (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
      BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (((((result,child.2),produced.2),supplied.2),all.2),controlled.2) := by
  simp only [framedWithControlExtras,framedWithFactoryExtras,BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.runWithFactoryExtras_compat,drawWithFactoryExtras_compat,fixedWithFactoryExtras_compat]

def framedWithRouteExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : (((((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ :=
  (framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header).1

theorem framedWithControlExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header).1 = framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header := rfl

theorem framedWithRouteExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header =


  let all := fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  let produced := BinaryPhysicalOutputMeasured.outputWithExtras parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList
  let output := produced.1
  let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
  let result :=
    (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
      BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  ((((result,child.2),produced.2),supplied.2),all.2) := by
  simp only [framedWithRouteExtras,framedWithControlExtras_record]
  rfl

def framedWithDrawOutputExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : ((((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ :=
  (framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header).1

theorem framedWithRouteExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header).1 = framedWithDrawOutputExtras backend frame parsed hParsed seed rich K outer scalar header := rfl

theorem framedWithDrawOutputExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    framedWithDrawOutputExtras backend frame parsed hParsed seed rich K outer scalar header =

  let supplied := fixedWithDrawExtras backend frame parsed hParsed seed rich K outer scalar
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  let produced := BinaryPhysicalOutputMeasured.outputWithExtras parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList
  let output := produced.1
  let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
  let result :=
    (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
      BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (((result,child.2),produced.2),supplied.2) := by
  simp only [framedWithDrawOutputExtras,framedWithRouteExtras_record]
  rfl

def framedWithOutputExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : (((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ :=
  (framedWithDrawOutputExtras backend frame parsed hParsed seed rich K outer scalar header).1

theorem framedWithDrawOutputExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framedWithDrawOutputExtras backend frame parsed hParsed seed rich K outer scalar header).1 = framedWithOutputExtras backend frame parsed hParsed seed rich K outer scalar header := rfl

theorem framedWithOutputExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    framedWithOutputExtras backend frame parsed hParsed seed rich K outer scalar header =
  let child := fixed backend frame parsed hParsed seed rich K outer scalar
  let returned := child.1
  let drawn := returned.1
  let produced := BinaryPhysicalOutputMeasured.outputWithExtras parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList
  let output := produced.1
  let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
  let result :=
    (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
      BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  ((result,child.2),produced.2) := by
  simp only [framedWithOutputExtras,framedWithDrawOutputExtras_record]
  rfl

def framed (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  (framedWithOutputExtras backend frame parsed hParsed seed rich K outer scalar header).1

theorem framedWithOutputExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framedWithOutputExtras backend frame parsed hParsed seed rich K outer scalar header).1 = framed backend frame parsed hParsed seed rich K outer scalar header := rfl

theorem framed_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    framed backend frame parsed hParsed seed rich K outer scalar header =
  let child := fixed backend frame parsed hParsed seed rich K outer scalar
  let returned := child.1
  let result :=
    let drawn := returned.1
    let output := BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a
      header.bytes drawn.1.1.1.1.data.toList
    let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
    (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
      BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (result,child.2) := by
  simp only [framed,framedWithOutputExtras_record,BinaryPhysicalOutputMeasured.outputWithExtras_compat]


theorem framed_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed backend frame parsed hParsed seed rich K outer scalar header).1 = BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header := by
  have h := fixed_compat backend frame parsed hParsed seed rich K outer scalar
  generalize hChild : fixed backend frame parsed hParsed seed rich K outer scalar = produced
  rcases produced with ⟨previous,price⟩
  rw [hChild] at h
  dsimp only at h
  rw [framed_record]
  rw [hChild]
  subst previous
  simp only [BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges]

set_option cleanup.letToHave false in
def seedWithFactoryExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : (((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      ((((((((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2),((0,0),0)),0),0),0),0),0)
  | some held =>
      let factoryReturned := framedWithFactoryExtras backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      let controlled := factoryReturned.1
      let all := controlled.1
      let collected := all.1
      let produced := collected.1
      let child := produced.1
      let returnedDraw := child.1
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      ((((((((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2),child.2),produced.2),collected.2),all.2),controlled.2),factoryReturned.2)

def seedWithControlExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ) × ℕ :=
  (seedWithFactoryExtras backend frame parsed hParsed rich seed).1

theorem seedWithFactoryExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (seedWithFactoryExtras backend frame parsed hParsed rich seed).1 = seedWithControlExtras backend frame parsed hParsed rich seed := rfl

theorem seedWithControlExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    seedWithControlExtras backend frame parsed hParsed rich seed =



  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      (((((((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2),((0,0),0)),0),0),0),0)
  | some held =>
      let controlled := framedWithControlExtras backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      let all := controlled.1
      let collected := all.1
      let produced := collected.1
      let child := produced.1
      let returnedDraw := child.1
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      (((((((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2),child.2),produced.2),collected.2),all.2),controlled.2) := by
  simp only [seedWithControlExtras,seedWithFactoryExtras,BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras_compat,BinaryWordTerminalCompleteMeasured.runWithFactoryExtras_compat,drawWithFactoryExtras_compat,fixedWithFactoryExtras_compat,framedWithFactoryExtras_compat]
  split <;> first | rfl | (split <;> rfl)

def seedWithRouteExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : (((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ) × ℕ :=
  (seedWithControlExtras backend frame parsed hParsed rich seed).1

theorem seedWithControlExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (seedWithControlExtras backend frame parsed hParsed rich seed).1 = seedWithRouteExtras backend frame parsed hParsed rich seed := rfl

theorem seedWithRouteExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    seedWithRouteExtras backend frame parsed hParsed rich seed =


  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      ((((((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2),((0,0),0)),0),0),0)
  | some held =>
      let all := framedWithRouteExtras backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      let collected := all.1
      let produced := collected.1
      let child := produced.1
      let returnedDraw := child.1
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      ((((((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2),child.2),produced.2),collected.2),all.2) := by
  simp only [seedWithRouteExtras,seedWithControlExtras_record]
  split <;> rfl

def seedWithDrawOutputExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ) × ℕ :=
  (seedWithRouteExtras backend frame parsed hParsed rich seed).1

theorem seedWithRouteExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (seedWithRouteExtras backend frame parsed hParsed rich seed).1 = seedWithDrawOutputExtras backend frame parsed hParsed rich seed := rfl

theorem seedWithDrawOutputExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    seedWithDrawOutputExtras backend frame parsed hParsed rich seed =

  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      (((((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2),((0,0),0)),0),0)
  | some held =>
      let collected := framedWithDrawOutputExtras backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      let produced := collected.1
      let child := produced.1
      let returnedDraw := child.1
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      (((((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2),child.2),produced.2),collected.2) := by
  simp only [seedWithDrawOutputExtras,seedWithRouteExtras_record]
  split <;> rfl

def seedWithOutputExtras (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : (((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E)) × ℕ :=
  (seedWithDrawOutputExtras backend frame parsed hParsed rich seed).1

theorem seedWithDrawOutputExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (seedWithDrawOutputExtras backend frame parsed hParsed rich seed).1 = seedWithOutputExtras backend frame parsed hParsed rich seed := rfl

theorem seedWithOutputExtras_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    seedWithOutputExtras backend frame parsed hParsed rich seed =
  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      ((((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2),((0,0),0)),0)
  | some held =>
      let produced := framedWithOutputExtras backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      let child := produced.1
      let returnedDraw := child.1
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      ((((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2),child.2),produced.2) := by
  simp only [seedWithOutputExtras,seedWithDrawOutputExtras_record]
  split <;> rfl

def seed (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  (seedWithOutputExtras backend frame parsed hParsed rich seed).1

theorem seedWithOutputExtras_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (seedWithOutputExtras backend frame parsed hParsed rich seed).1 = BinaryCacheContinuationCore.seed backend frame parsed hParsed rich seed := rfl

theorem seed_record (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    BinaryCacheContinuationCore.seed backend frame parsed hParsed rich seed =
  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      (((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2),((0,0),0))
  | some held =>
      let child := framed backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      let returnedDraw := child.1
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      (((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2),child.2) := by
  simp only [BinaryCacheContinuationCore.seed,seedWithOutputExtras_record]
  cases h : (BinarySeedPreparationEmission.prepare parsed.1.2.logical seed).1.1.1 with
  | none => simp only [h]
  | some held => simp only [h,framedWithOutputExtras_compat]


theorem seed_compat (backend : Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed backend frame parsed hParsed rich bits).1 = BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits := by
  rw [seed_record]
  unfold BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges
  dsimp only
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i held hSome
    simp only [hSome,framed_compat]

def raw (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,((0,0),0))
  | some parsed =>
      if parsed.2 = [] then
        let child := seed backend frame parsed hParsed rich bits
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (result,child.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (result,((0,0),0))

theorem raw_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (raw backend rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits := by
  unfold raw BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_compat]
      · simp only [ite_eq_right hTail]


def parsedRaw (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,((0,0),0))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let child := seed backend frame parsed hOriginal rich bits
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (result,child.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (result,((0,0),0))

theorem parsedRaw_compat (backend : Backend E) (rich : Bool) (frame bits : List Bool) :
    (parsedRaw backend rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits := by
  unfold parsedRaw BinaryTerminalPhysicalParsedRawMeasured.runWithCharges
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_compat]
      · simp only [ite_eq_right hTail]


def generated (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,((0,0),0))
  | some parsed =>
      if parsed.2 = [] then
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := seed backend frame parsed hParsed rich generated.1.1.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (result,child.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (result,((0,0),0))

theorem generated_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated backend next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state := by
  unfold generated BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_compat]
      · simp only [ite_eq_right hTail]


def parsedGenerated (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,((0,0),0))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := seed backend frame parsed hOriginal rich generated.1.1.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (result,child.2)
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (result,((0,0),0))

theorem parsedGenerated_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated backend next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state := by
  unfold parsedGenerated BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_compat]
      · simp only [ite_eq_right hTail]


def pair (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let first := generated backend next true frame state
  let rich := first.1
  let second := generated backend next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2))

theorem pair_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair backend next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state := by
  simp only [pair,BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration,generated_compat]

def parsedPair (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × E) :=
  let first := parsedGenerated backend next true frame state
  let rich := first.1
  let second := parsedGenerated backend next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2))

theorem parsedPair_compat (backend : Backend E) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair backend next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state := by
  simp only [parsedPair,BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration,parsedGenerated_compat]


def OldPrices (backend : Backend E) : Prop :=
  ∀ (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool),
    (backend.run parsed seed rich).2.1 = (BinaryInitializerEmissionExecution.cache parsed seed rich).2

theorem certified_oldPrices (backend : Backend E) (hCache : OldPrices backend) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified backend frame parsed hParsed seed rich).2.1 = (BinaryInitializerEmissionExecution.certified frame parsed hParsed seed rich).2 := by
  exact hCache parsed.1 seed rich

theorem draw_oldPrices (backend : Backend E) (hCache : OldPrices backend) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw backend frame parsed hParsed seed rich K outer scalar).2.1 = (BinaryInitializerEmissionExecution.draw frame parsed hParsed seed rich K outer scalar).2 := by
  exact certified_oldPrices backend hCache frame parsed hParsed seed rich

theorem fixed_oldPrices (backend : Backend E) (hCache : OldPrices backend) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed backend frame parsed hParsed seed rich K outer scalar).2.1 = (BinaryInitializerEmissionExecution.fixed frame parsed hParsed seed rich K outer scalar).2 := by
  exact draw_oldPrices backend hCache frame parsed hParsed seed rich K outer scalar

theorem framed_oldPrices (backend : Backend E) (hCache : OldPrices backend) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed backend frame parsed hParsed seed rich K outer scalar header).2.1 = (BinaryInitializerEmissionExecution.framed frame parsed hParsed seed rich K outer scalar header).2 := by
  exact fixed_oldPrices backend hCache frame parsed hParsed seed rich K outer scalar

theorem seed_oldPrices (backend : Backend E) (hCache : OldPrices backend) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed backend frame parsed hParsed rich bits).2.1 = (BinaryInitializerEmissionExecution.seed frame parsed hParsed rich bits).2 := by
  rw [seed_record]
  unfold BinaryInitializerEmissionExecution.seed
  dsimp only
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i held hSome
    simp only [hSome,framed_oldPrices backend hCache]

theorem raw_oldPrices (backend : Backend E) (hCache : OldPrices backend) (rich : Bool) (frame bits : List Bool) :
    (raw backend rich frame bits).2.1 = (BinaryInitializerEmissionExecution.raw rich frame bits).2 := by
  unfold raw BinaryInitializerEmissionExecution.raw
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_oldPrices backend hCache]
      · simp only [ite_eq_right hTail]

theorem parsedRaw_oldPrices (backend : Backend E) (hCache : OldPrices backend) (rich : Bool) (frame bits : List Bool) :
    (parsedRaw backend rich frame bits).2.1 = (BinaryInitializerEmissionExecution.parsedRaw rich frame bits).2 := by
  unfold parsedRaw BinaryInitializerEmissionExecution.parsedRaw
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_oldPrices backend hCache]
      · simp only [ite_eq_right hTail]

theorem generated_oldPrices (backend : Backend E) (hCache : OldPrices backend) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated backend next rich frame state).2.1 = (BinaryInitializerEmissionExecution.generated next rich frame state).2 := by
  unfold generated BinaryInitializerEmissionExecution.generated
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_oldPrices backend hCache]
      · simp only [ite_eq_right hTail]

theorem parsedGenerated_oldPrices (backend : Backend E) (hCache : OldPrices backend) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated backend next rich frame state).2.1 = (BinaryInitializerEmissionExecution.parsedGenerated next rich frame state).2 := by
  unfold parsedGenerated BinaryInitializerEmissionExecution.parsedGenerated
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i other hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,seed_oldPrices backend hCache]
      · simp only [ite_eq_right hTail]

theorem pair_oldPrices (backend : Backend E) (hCache : OldPrices backend) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair backend next frame state).2.1 = (BinaryInitializerEmissionExecution.pair next frame state).2 := by
  simp only [pair,BinaryInitializerEmissionExecution.pair,generated_oldPrices backend hCache,
    generated_compat,BinaryInitializerEmissionExecution.generated_compat]

theorem parsedPair_oldPrices (backend : Backend E) (hCache : OldPrices backend) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair backend next frame state).2.1 = (BinaryInitializerEmissionExecution.parsedPair next frame state).2 := by
  simp only [parsedPair,BinaryInitializerEmissionExecution.parsedPair,parsedGenerated_oldPrices backend hCache,
    parsedGenerated_compat,BinaryInitializerEmissionExecution.parsedGenerated_compat]

end Blotto.BinaryCacheContinuationCore
