import Blotto.BinaryPhysicalCachePlan
import Blotto.BinaryCacheEmissionBounds
import Blotto.BinaryAllowanceEmissionRequest

/-! A complete actual continuation carries cache emission and initializer
calculator emission as distinct counters. Each reached child is consumed once;
all preceding records, ledgers, rejection and sequential-state behavior refine
the former complete path. Other machine/runtime obligations remain explicit. -/
namespace Blotto.BinaryInitializerEmissionExecution
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryTerminalCacheCertificate
set_option autoImplicit false
set_option maxHeartbeats 3000000

def cache (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) ×
      BinaryExecutionCharges.Charges) × (ℕ × ℕ) :=
  let initialized := BinaryAllowanceEmissionRequest.runWithCharges seed parsed.2 rich
  let returned := initialized.1
  let resource := returned.1
  match resource.1.1.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 resource.1.2
      ((((((none,resource.1.1.1.2),resource.1.1.2),emitted.1),resource.2+4),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2),(0,initialized.2))
  | some state =>
      let produced := BinaryPhysicalCachePlan.cacheWithEmission
        (terminalInput parsed.2.logical.request rich state) parsed.2.physical.lengthStore
      let cached := produced.1
      let emitted := BinaryWrapperEmission.two 24 2 resource.1.2 cached.1.2
      ((((((some ⟨state,cached.1.1⟩,resource.1.1.1.2),resource.1.1.2),emitted.1),resource.2+cached.2+8),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2),(produced.2,initialized.2))

theorem cache_compat (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache parsed seed rich).1 = BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich := by
  unfold cache BinaryTerminalPhysicalAllowanceCache.runWithCharges
  dsimp only
  simp only [BinaryAllowanceEmissionRequest.runWithCharges_compat]
  split
  · rename_i hNone
    simp only [hNone,BinaryWrapperEmission.one]
  · rename_i state hSome
    simp only [hSome,BinaryPhysicalCachePlan.cacheWithEmission_compat,BinaryWrapperEmission.two]


def certified (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (((((Option (BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich) × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) × BinaryExecutionCharges.Charges) × (ℕ × ℕ) :=
  let child := cache parsed.1 seed rich
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
            (by simpa only [observed,returned,child,cache_compat,BinaryTerminalPhysicalAllowanceCache.run] using hs))
        let emitted := BinaryWrapperEmission.two 24 2 observed.1.2 certified.2
        (((((some ⟨result.1,certified.1⟩,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2),
          BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (result,child.2)

theorem certified_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified frame parsed hParsed seed rich).1 = BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich := by
  have hData := congrArg (fun produced => produced.1.1.1.1.1) (cache_compat parsed.1 seed rich)
  unfold certified BinaryTerminalPhysicalAllowanceCertified.runWithCharges
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [cache_compat]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      simp only [cache_compat]


def draw (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × (ℕ × ℕ) :=
  let request := parsed.1.2.logical.request
  let child := certified frame parsed hParsed seed rich
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
  (result,child.2)

theorem draw_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar := by
  have hData := congrArg (fun produced => produced.1.1.1.1.1) (certified_compat frame parsed hParsed seed rich)
  unfold draw BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges
  dsimp only
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


def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × (ℕ × ℕ) :=
  let child := draw frame parsed hParsed seed rich K outer scalar
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
  (result,child.2)

theorem fixed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).1 = BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar := by
  have hData := congrArg (fun produced => produced.1.1.1.1.1) (draw_compat frame parsed hParsed seed rich K outer scalar)
  unfold fixed BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges
  dsimp only
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


def framed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges) × (ℕ × ℕ) :=
  let child := fixed frame parsed hParsed seed rich K outer scalar
  let returned := child.1
  let result :=
    let drawn := returned.1
    let output := BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a
      header.bytes drawn.1.1.1.1.data.toList
    let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
    (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
      BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  (result,child.2)

theorem framed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed frame parsed hParsed seed rich K outer scalar header).1 = BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar header := by
  have h := fixed_compat frame parsed hParsed seed rich K outer scalar
  generalize hChild : fixed frame parsed hParsed seed rich K outer scalar = produced
  rcases produced with ⟨previous,price⟩
  rw [hChild] at h
  dsimp only at h
  unfold framed
  rw [hChild]
  subst previous
  simp only [BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges]

def seed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × (ℕ × ℕ) :=
  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      (((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2),(0,0))
  | some held =>
      let child := framed frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      let returnedDraw := child.1
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      (((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2),child.2)

theorem seed_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed frame parsed hParsed rich bits).1 = BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich bits := by
  unfold seed BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges
  dsimp only
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i held hSome
    simp only [hSome,framed_compat]

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × (ℕ × ℕ) :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,(0,0))
  | some parsed =>
      if parsed.2 = [] then
        let child := seed frame parsed hParsed rich bits
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
        (result,(0,0))

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits := by
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


def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × (ℕ × ℕ) :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,(0,0))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let child := seed frame parsed hOriginal rich bits
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
        (result,(0,0))

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits := by
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


def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × (ℕ × ℕ) :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,(0,0))
  | some parsed =>
      if parsed.2 = [] then
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := seed
          frame parsed hParsed rich generated.1.1.1
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
        (result,(0,0))

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state := by
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


def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × (ℕ × ℕ) :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,(0,0))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := seed
          frame parsed hOriginal rich generated.1.1.1
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
        (result,(0,0))

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state := by
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


def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × (ℕ × ℕ) :=
  let first := generated next true frame state
  let rich := first.1
  let second := generated next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,(first.2.1+second.2.1,first.2.2+second.2.2))

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state := by
  simp only [pair,BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration,generated_compat]

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × (ℕ × ℕ) :=
  let first := parsedGenerated next true frame state
  let rich := first.1
  let second := parsedGenerated next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,(first.2.1+second.2.1,first.2.2+second.2.2))

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state := by
  simp only [parsedPair,BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration,parsedGenerated_compat]

/-- Forget only the new initializer price, retaining the prior cache price. -/
def preceding {α : Type*} (produced : α × (ℕ × ℕ)) : α × ℕ := (produced.1,produced.2.1)

theorem cache_cacheEmission (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (cache parsed seed rich).2.1 = (BinaryCacheEmissionExecution.cache parsed seed rich).2 := by
  unfold cache BinaryCacheEmissionExecution.cache
  dsimp only
  simp only [BinaryAllowanceEmissionRequest.runWithCharges_compat]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i state hSome
    simp only [hSome]

theorem certified_cacheEmission (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (certified frame parsed hParsed seed rich).2.1 = (BinaryCacheEmissionExecution.certified frame parsed hParsed seed rich).2 := by
  exact cache_cacheEmission parsed.1 seed rich

theorem draw_cacheEmission (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).2.1 = (BinaryCacheEmissionExecution.draw frame parsed hParsed seed rich K outer scalar).2 := by
  exact certified_cacheEmission frame parsed hParsed seed rich

theorem fixed_cacheEmission (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).2.1 = (BinaryCacheEmissionExecution.fixed frame parsed hParsed seed rich K outer scalar).2 := by
  exact draw_cacheEmission frame parsed hParsed seed rich K outer scalar

theorem framed_cacheEmission (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (framed frame parsed hParsed seed rich K outer scalar header).2.1 = (BinaryCacheEmissionExecution.framed frame parsed hParsed seed rich K outer scalar header).2 := by
  exact fixed_cacheEmission frame parsed hParsed seed rich K outer scalar

theorem seed_cacheEmission (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    (seed frame parsed hParsed rich bits).2.1 = (BinaryCacheEmissionExecution.seed frame parsed hParsed rich bits).2 := by
  unfold seed BinaryCacheEmissionExecution.seed
  dsimp only
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i held hSome
    simp only [hSome,framed_cacheEmission]

theorem raw_cacheEmission (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).2.1 = (BinaryCacheEmissionExecution.raw rich frame bits).2 := by
  unfold raw BinaryCacheEmissionExecution.raw
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
      · simp only [ite_eq_left hTail,seed_cacheEmission]
      · simp only [ite_eq_right hTail]


theorem parsedRaw_cacheEmission (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).2.1 = (BinaryCacheEmissionExecution.parsedRaw rich frame bits).2 := by
  unfold parsedRaw BinaryCacheEmissionExecution.parsedRaw
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
      · simp only [ite_eq_left hTail,seed_cacheEmission]
      · simp only [ite_eq_right hTail]


theorem generated_cacheEmission {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (generated next rich frame state).2.1 = (BinaryCacheEmissionExecution.generated next rich frame state).2 := by
  unfold generated BinaryCacheEmissionExecution.generated
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
      · simp only [ite_eq_left hTail,seed_cacheEmission]
      · simp only [ite_eq_right hTail]


theorem parsedGenerated_cacheEmission {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).2.1 = (BinaryCacheEmissionExecution.parsedGenerated next rich frame state).2 := by
  unfold parsedGenerated BinaryCacheEmissionExecution.parsedGenerated
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
      · simp only [ite_eq_left hTail,seed_cacheEmission]
      · simp only [ite_eq_right hTail]


theorem pair_cacheEmission {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).2.1 = (BinaryCacheEmissionExecution.pair next frame state).2 := by
  simp only [pair,BinaryCacheEmissionExecution.pair,generated_cacheEmission,
    generated_compat,BinaryCacheEmissionExecution.generated_compat]

theorem parsedPair_cacheEmission {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).2.1 = (BinaryCacheEmissionExecution.parsedPair next frame state).2 := by
  simp only [parsedPair,BinaryCacheEmissionExecution.parsedPair,parsedGenerated_cacheEmission,
    parsedGenerated_compat,BinaryCacheEmissionExecution.parsedGenerated_compat]

theorem cache_preceding (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    preceding (cache parsed seed rich) = BinaryCacheEmissionExecution.cache parsed seed rich :=
  Prod.ext ((cache_compat parsed seed rich).trans (BinaryCacheEmissionExecution.cache_compat parsed seed rich).symm)
    (cache_cacheEmission parsed seed rich)

theorem certified_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    preceding (certified frame parsed hParsed seed rich) = BinaryCacheEmissionExecution.certified frame parsed hParsed seed rich :=
  Prod.ext ((certified_compat frame parsed hParsed seed rich).trans (BinaryCacheEmissionExecution.certified_compat frame parsed hParsed seed rich).symm)
    (certified_cacheEmission frame parsed hParsed seed rich)

theorem draw_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    preceding (draw frame parsed hParsed seed rich K outer scalar) = BinaryCacheEmissionExecution.draw frame parsed hParsed seed rich K outer scalar :=
  Prod.ext ((draw_compat frame parsed hParsed seed rich K outer scalar).trans (BinaryCacheEmissionExecution.draw_compat frame parsed hParsed seed rich K outer scalar).symm)
    (draw_cacheEmission frame parsed hParsed seed rich K outer scalar)

theorem fixed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    preceding (fixed frame parsed hParsed seed rich K outer scalar) = BinaryCacheEmissionExecution.fixed frame parsed hParsed seed rich K outer scalar :=
  Prod.ext ((fixed_compat frame parsed hParsed seed rich K outer scalar).trans (BinaryCacheEmissionExecution.fixed_compat frame parsed hParsed seed rich K outer scalar).symm)
    (fixed_cacheEmission frame parsed hParsed seed rich K outer scalar)

theorem framed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    preceding (framed frame parsed hParsed seed rich K outer scalar header) = BinaryCacheEmissionExecution.framed frame parsed hParsed seed rich K outer scalar header :=
  Prod.ext ((framed_compat frame parsed hParsed seed rich K outer scalar header).trans (BinaryCacheEmissionExecution.framed_compat frame parsed hParsed seed rich K outer scalar header).symm)
    (framed_cacheEmission frame parsed hParsed seed rich K outer scalar header)

theorem seed_preceding (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    preceding (seed frame parsed hParsed rich bits) = BinaryCacheEmissionExecution.seed frame parsed hParsed rich bits :=
  Prod.ext ((seed_compat frame parsed hParsed rich bits).trans (BinaryCacheEmissionExecution.seed_compat frame parsed hParsed rich bits).symm)
    (seed_cacheEmission frame parsed hParsed rich bits)

theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    preceding (raw rich frame bits) = BinaryCacheEmissionExecution.raw rich frame bits :=
  Prod.ext ((raw_compat rich frame bits).trans (BinaryCacheEmissionExecution.raw_compat rich frame bits).symm)
    (raw_cacheEmission rich frame bits)

theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    preceding (parsedRaw rich frame bits) = BinaryCacheEmissionExecution.parsedRaw rich frame bits :=
  Prod.ext ((parsedRaw_compat rich frame bits).trans (BinaryCacheEmissionExecution.parsedRaw_compat rich frame bits).symm)
    (parsedRaw_cacheEmission rich frame bits)

theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    preceding (generated next rich frame state) = BinaryCacheEmissionExecution.generated next rich frame state :=
  Prod.ext ((generated_compat next rich frame state).trans (BinaryCacheEmissionExecution.generated_compat next rich frame state).symm)
    (generated_cacheEmission next rich frame state)

theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    preceding (parsedGenerated next rich frame state) = BinaryCacheEmissionExecution.parsedGenerated next rich frame state :=
  Prod.ext ((parsedGenerated_compat next rich frame state).trans (BinaryCacheEmissionExecution.parsedGenerated_compat next rich frame state).symm)
    (parsedGenerated_cacheEmission next rich frame state)

theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    preceding (pair next frame state) = BinaryCacheEmissionExecution.pair next frame state :=
  Prod.ext ((pair_compat next frame state).trans (BinaryCacheEmissionExecution.pair_compat next frame state).symm)
    (pair_cacheEmission next frame state)

theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    preceding (parsedPair next frame state) = BinaryCacheEmissionExecution.parsedPair next frame state :=
  Prod.ext ((parsedPair_compat next frame state).trans (BinaryCacheEmissionExecution.parsedPair_compat next frame state).symm)
    (parsedPair_cacheEmission next frame state)

end Blotto.BinaryInitializerEmissionExecution
