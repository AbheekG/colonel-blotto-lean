import Blotto.BinaryFourGroupFactoryExtras
import Blotto.BinaryReturnedControlExtras

/-! Actual factory costs reach every complete request. Earlier four fields and
all27 source-ledger terms remain exact. Native and physical joins are separate. -/
namespace Blotto.BinaryReturnedFactoryExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryCachedTerminalPreparation
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryTerminalCacheCertificate
open BinaryFactoryHeight BinaryExpressionCompiler
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryReturnedOutputExtras (join_source_component)
set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local irreducible] BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras BinaryWordTerminalCompleteMeasured.runWithFactoryExtras BinaryCacheContinuationCore.drawWithFactoryExtras BinaryCacheContinuationCore.fixedWithFactoryExtras BinaryCacheContinuationCore.framedWithFactoryExtras BinaryCacheContinuationCore.seedWithFactoryExtras BinaryCacheFinishRequest.seedWithFactoryExtras BinaryRawParserContinuation.rawWithFactoryExtras BinaryRawParserContinuation.parsedRawWithFactoryExtras BinaryRawParserContinuation.generatedWithFactoryExtras BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras BinaryRawParserContinuation.pairWithFactoryExtras BinaryRawParserContinuation.parsedPairWithFactoryExtras BinaryPromiseOpcodeRequest.rawWithFactoryExtras BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras BinaryPromiseOpcodeRequest.generatedWithFactoryExtras BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras BinaryPromiseOpcodeRequest.pairWithFactoryExtras BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras BinaryWordGroupDrawMeasured.uniformRunWithFactoryExtras BinaryWordGroupDrawMeasured.mixedTwoRunWithFactoryExtras BinaryFourRestoredMeasured.runWithFactoryExtras BinaryGroupEmissionMeasured.emitOptionWithExtras BinaryWordGroupCompleteMeasured.afterMixedWithRouteExtras

theorem uniform_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).1.1.2+(BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).1.1.1.2 := by
  have hd := BinaryFourGroupFactoryExtras.GroupDraw.uniformRun_combined store input hC hAd hm K scalar pc hp
  have he := BinaryReturnedRouteExtras.option_bound routes (BinaryWordGroupDrawMeasured.uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1.1.1.1.1
  simp only [BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras,BinaryWordGroupCompleteMeasured.collect]
  omega

theorem mixed_two_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).1.1.2+(BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).1.1.1.2 := by
  let all := BinaryWordGroupDrawMeasured.mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp
  have hd := BinaryFourGroupFactoryExtras.GroupDraw.mixedTwoRun_combined store input hC hAd K scalar pc hp
  have he := BinaryReturnedRouteExtras.after_mixed_joint store routes pivot all.1.1 (all.1.2+all.2) hd
  dsimp only [all] at he
  simp only [BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras]
  omega

theorem draw_two_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.1.2+(BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.1.1.2 := by
  subst m
  simpa only [BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras] using mixed_two_bound store input hC hAd routes pivot K scalar pc hp

theorem mixed_three_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).1.1.1.2+(BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).1.1.2+(BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).1.1.1.1.2 := by
  let all := BinaryFourRestoredMeasured.runWithFactoryExtras store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  have hd := BinaryFourGroupFactoryExtras.Restored.run_combined store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp
  have he := BinaryReturnedRouteExtras.after_mixed_joint store routes pivot all.1.1.1 (all.1.1.2+all.1.2+all.2) hd
  dsimp only [all] at he
  simp only [BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras]
  omega


theorem draw_three_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.1.1.2+(BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.1.2+(BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.1.1.1.2 := by
  subst m
  simpa only [BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras] using mixed_three_bound store input hC hAd routes pivot K outer scalar pc hp


theorem terminal_bound {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).1.1.1.2+(BinaryWordTerminalCompleteMeasured.runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).1.1.2+(BinaryWordTerminalCompleteMeasured.runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).1.1.1.1.2 := by
  simp only [BinaryWordTerminalCompleteMeasured.runWithFactoryExtras]
  split
  · rename_i hPivot
    have h := uniform_bound store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
    dsimp only [BinaryWordTerminalCompleteMeasured.branch]
    omega
  · rename_i selected hPivot
    split
    · rename_i hTwo
      have h := draw_two_bound store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected K scalar pc hp
      dsimp only [BinaryWordTerminalCompleteMeasured.branch]
      omega
    · rename_i hTwo
      have h := draw_three_bound store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp
      dsimp only [BinaryWordTerminalCompleteMeasured.branch]
      omega


theorem draw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryCacheContinuationCore.drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.2+(BinaryCacheContinuationCore.drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.2+(BinaryCacheContinuationCore.drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.2+(BinaryCacheContinuationCore.drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.1.1.2 := by
  let request := parsed.1.2.logical.request
  let child := BinaryCacheContinuationCore.certified backend frame parsed hParsed seed rich
  let returned := child.1
  let observed := returned.1
  simp only [BinaryCacheContinuationCore.drawWithFactoryExtras]
  split
  · dsimp only; omega
  · rename_i result hs
    have h := terminal_bound seed result.2
          (terminal_canonical request rich result.1)
          (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
            (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result
              (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using hs)))
          K outer scalar observed.1.1.1.2 (by simpa only [observed,returned,child,BinaryCacheContinuationCore.certified_compat,BinaryTerminalPhysicalAllowanceCertified.run] using
            (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
    dsimp only [request,observed,returned,child] at h
    dsimp only
    omega


theorem fixed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.2+(BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.2+(BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.2+(BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.1.1.2 := by
  have h := draw_bound backend frame parsed hParsed seed rich K outer scalar
  simp only [BinaryCacheContinuationCore.fixedWithFactoryExtras]
  split <;> dsimp only <;> omega


theorem framed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.1.2+(BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.2+(BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.2+(BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1.2)+(BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).2 ≤
      155*(BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.1.1.1.1.2 := by
  let factoryControlled := BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar
  let controlled := factoryControlled.1
  let all := controlled.1
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  have hd := fixed_bound backend frame parsed hParsed seed rich K outer scalar
  have ho := BinaryReturnedOutputExtras.output_bound parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  dsimp only [drawn,returned,child,supplied,all,controlled,factoryControlled] at ho
  simp only [BinaryCacheContinuationCore.framedWithFactoryExtras]
  omega



theorem seed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    ((BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).1.1.1.1.2+(BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).1.1.1.2+(BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).1.1.2+(BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).1.2)+(BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).2 ≤
      155*(BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).1.1.1.1.1.1.1.2 := by
  simp only [BinaryCacheContinuationCore.seedWithFactoryExtras]
  cases h : (BinarySeedPreparationEmission.prepare parsed.1.2.logical bits).1.1.1 with
  | none => dsimp only; omega
  | some held =>
      dsimp only
      have he := framed_bound backend frame parsed hParsed held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      omega


theorem cache_seed_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    ((BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).1.1.1.1.2+(BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).1.1.1.2+(BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).1.1.2+(BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).1.2)+(BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).2 ≤
      155*(BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).1.1.1.1.1.1.1.2 := by
  simpa only [BinaryCacheFinishRequest.seedWithFactoryExtras] using seed_bound BinaryCacheFinishRequest.backend frame parsed hParsed rich bits


theorem parser_raw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    ((BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).1.1.1.1.2+(BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).1.1.1.2+(BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).1.1.2+(BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).1.2)+(BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).2 ≤ 155*(BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).1.1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.rawWithFactoryExtras]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      have hc := cache_seed_bound frame parsed hOriginal rich bits
      dsimp only
      omega
    · dsimp only; omega


theorem parser_parsedRaw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    ((BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).1.1.1.1.2+(BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).1.1.1.2+(BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).1.1.2+(BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).1.2)+(BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).2 ≤ 155*(BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).1.1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedRawWithFactoryExtras]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      have hc := cache_seed_bound frame parsed hOriginal rich bits
      dsimp only
      omega
    · dsimp only; omega


theorem parser_generated_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).1.1.1.1.2+(BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).1.1.1.2+(BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).1.1.2+(BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).1.2)+(BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).2 ≤ 155*(BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).1.1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.generatedWithFactoryExtras]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
      let generated := generation.1
      have hc := cache_seed_bound frame parsed hOriginal rich generated.1.1.1
      dsimp only [generated,generation] at hc
      dsimp only
      omega
    · dsimp only; omega


theorem parser_parsedGenerated_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).1.1.1.1.2+(BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).1.1.1.2+(BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).1.1.2+(BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).1.2)+(BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).2 ≤ 155*(BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).1.1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras]
  split
  · dsimp only; omega
  · rename_i parsed hParsed
    split
    · have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
        (congrArg Prod.fst (BinaryRawParserContinuation.read_original backend frame)).symm.trans hParsed
      let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
      let generated := generation.1
      have hc := cache_seed_bound frame parsed hOriginal rich generated.1.1.1
      dsimp only [generated,generation] at hc
      dsimp only
      omega
    · dsimp only; omega


theorem parser_pair_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).1.1.1.1.2+(BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).1.1.1.2+(BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).1.1.2+(BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).1.2)+(BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).2 ≤ 155*(BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).1.1.1.1.1.1.1.2 := by
  let factoryFirst := BinaryRawParserContinuation.generatedWithFactoryExtras backend next true frame state
  let first := factoryFirst.1
  let rich := first.1.1.1.1.1
  have hFirst := parser_generated_bound backend next true frame state
  have hSecond := parser_generated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first,factoryFirst] at hSecond
  simp only [BinaryRawParserContinuation.pairWithFactoryExtras]
  omega


theorem parser_parsedPair_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).1.1.1.1.2+(BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).1.1.1.2+(BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).1.1.2+(BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).1.2)+(BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).2 ≤ 155*(BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).1.1.1.1.1.1.1.2 := by
  let factoryFirst := BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next true frame state
  let first := factoryFirst.1
  let rich := first.1.1.1.1.1
  have hFirst := parser_parsedGenerated_bound backend next true frame state
  have hSecond := parser_parsedGenerated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first,factoryFirst] at hSecond
  simp only [BinaryRawParserContinuation.parsedPairWithFactoryExtras]
  omega


theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.2+(BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.2+(BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.2+(BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.2)+(BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).2 ≤ 155*(BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.rawWithFactoryExtras] using parser_raw_bound BinaryPromiseOpcodeRequest.backend rich frame bits


theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.2+(BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.2+(BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.2+(BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.2)+(BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).2 ≤ 155*(BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras] using parser_parsedRaw_bound BinaryPromiseOpcodeRequest.backend rich frame bits


theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.2+(BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.2+(BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.2)+(BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.generatedWithFactoryExtras] using parser_generated_bound BinaryPromiseOpcodeRequest.backend next rich frame state


theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.2)+(BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras] using parser_parsedGenerated_bound BinaryPromiseOpcodeRequest.backend next rich frame state


theorem pair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.2+(BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.2+(BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.2)+(BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1.1.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.pairWithFactoryExtras] using parser_pair_bound BinaryPromiseOpcodeRequest.backend next frame state


theorem parsedPair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.2+(BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.2+(BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.2)+(BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).2 ≤ 155*(BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1.1.1.2 := by
  simpa only [BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras] using parser_parsedPair_bound BinaryPromiseOpcodeRequest.backend next frame state

theorem uniform_factory  {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).1.1.1.2 := by
  have h := uniform_bound store input hC hAd hm routes K scalar pc hp
  omega

theorem mixed_two_factory  {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).1.1.1.2 := by
  have h := mixed_two_bound store input hC hAd routes pivot K scalar pc hp
  omega

theorem draw_two_factory  {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.1.1.2 := by
  have h := draw_two_bound store input hC hAd hTwo routes pivot K scalar pc hp
  omega

theorem mixed_three_factory  {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).1.1.1.1.2 := by
  have h := mixed_three_bound store input hC hAd routes pivot K outer scalar pc hp
  omega

theorem draw_three_factory  {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.1.1.1.2 := by
  have h := draw_three_bound store input hC hAd hThree routes pivot K outer scalar pc hp
  omega

theorem terminal_factory  {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (BinaryWordTerminalCompleteMeasured.runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).1.1.1.1.2 := by
  have h := terminal_bound store prepared hC hAd K outer scalar pc hp
  omega

theorem draw_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)  :
    (BinaryCacheContinuationCore.drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.drawWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.1.1.2 := by
  have h := draw_bound backend frame parsed hParsed seed rich K outer scalar
  omega

theorem fixed_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E) (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)  :
    (BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.fixedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.1.1.2 := by
  have h := fixed_bound backend frame parsed hParsed seed rich K outer scalar
  omega

theorem framed_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1)  :
    (BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).2 ≤155*(BinaryCacheContinuationCore.framedWithFactoryExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.1.1.1.1.2 := by
  have h := framed_bound backend frame parsed hParsed seed rich K outer scalar header
  omega

theorem seed_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool)  :
    (BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).2 ≤155*(BinaryCacheContinuationCore.seedWithFactoryExtras backend frame parsed hParsed rich bits).1.1.1.1.1.1.1.2 := by
  have h := seed_bound backend frame parsed hParsed rich bits
  omega

theorem cache_seed_factory  (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool)  :
    (BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).2 ≤155*(BinaryCacheFinishRequest.seedWithFactoryExtras frame parsed hParsed rich bits).1.1.1.1.1.1.1.2 := by
  have h := cache_seed_bound frame parsed hParsed rich bits
  omega

theorem parser_raw_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool)  :
    (BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).2 ≤155*(BinaryRawParserContinuation.rawWithFactoryExtras backend rich frame bits).1.1.1.1.1.1.1.2 := by
  have h := parser_raw_bound backend rich frame bits
  omega

theorem parser_parsedRaw_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool)  :
    (BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).2 ≤155*(BinaryRawParserContinuation.parsedRawWithFactoryExtras backend rich frame bits).1.1.1.1.1.1.1.2 := by
  have h := parser_parsedRaw_bound backend rich frame bits
  omega

theorem parser_generated_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)  :
    (BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).2 ≤155*(BinaryRawParserContinuation.generatedWithFactoryExtras backend next rich frame state).1.1.1.1.1.1.1.2 := by
  have h := parser_generated_bound backend next rich frame state
  omega

theorem parser_parsedGenerated_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)  :
    (BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).2 ≤155*(BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend next rich frame state).1.1.1.1.1.1.1.2 := by
  have h := parser_parsedGenerated_bound backend next rich frame state
  omega

theorem parser_pair_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S)  :
    (BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).2 ≤155*(BinaryRawParserContinuation.pairWithFactoryExtras backend next frame state).1.1.1.1.1.1.1.2 := by
  have h := parser_pair_bound backend next frame state
  omega

theorem parser_parsedPair_factory  {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S)  :
    (BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).2 ≤155*(BinaryRawParserContinuation.parsedPairWithFactoryExtras backend next frame state).1.1.1.1.1.1.1.2 := by
  have h := parser_parsedPair_bound backend next frame state
  omega

theorem raw_factory  (rich : Bool) (frame bits : List Bool)  :
    (BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).2 ≤155*(BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.2 := by
  have h := raw_bound rich frame bits
  omega

theorem parsedRaw_factory  (rich : Bool) (frame bits : List Bool)  :
    (BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).2 ≤155*(BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.2 := by
  have h := parsedRaw_bound rich frame bits
  omega

theorem generated_factory  {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)  :
    (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).2 ≤155*(BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.2 := by
  have h := generated_bound next rich frame state
  omega

theorem parsedGenerated_factory  {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)  :
    (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).2 ≤155*(BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.2 := by
  have h := parsedGenerated_bound next rich frame state
  omega

theorem pair_factory  {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S)  :
    (BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).2 ≤155*(BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1.1.1.2 := by
  have h := pair_bound next frame state
  omega

theorem parsedPair_factory  {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S)  :
    (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).2 ≤155*(BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1.1.1.2 := by
  have h := parsedPair_bound next frame state
  omega

attribute [local irreducible]
  BinaryPromiseOpcodeRequest.raw
  BinaryPromiseOpcodeRequest.parsedRaw
  BinaryPromiseOpcodeRequest.generated
  BinaryPromiseOpcodeRequest.parsedGenerated
  BinaryPromiseOpcodeRequest.pair
  BinaryPromiseOpcodeRequest.parsedPair
  BinaryPromiseOpcodeRequest.rawWithOutputExtras
  BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras
  BinaryPromiseOpcodeRequest.generatedWithOutputExtras
  BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras
  BinaryPromiseOpcodeRequest.pairWithOutputExtras
  BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras
  BinaryCompleteRequestArithmeticEntryWork.rawCost
  BinaryCompleteRequestArithmeticEntryWork.generatedCost
  BinaryCompleteRequestArithmeticEntryWork.pairCost
  BinaryCompleteRequestArithmeticEntryWork.parsedPairCost
attribute [local irreducible]
  BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras
  BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras
attribute [local irreducible] BinaryPRGHeapTraceUsage.usage BinarySamplerExecutionCharges.total
  BinaryGenerationExecutionCharges.total BinaryBigEndian.littleValue
set_option maxHeartbeats 300000

attribute [local irreducible]
  BinaryPromiseOpcodeRequest.rawWithRouteExtras
  BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras
  BinaryPromiseOpcodeRequest.generatedWithRouteExtras
  BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras
  BinaryPromiseOpcodeRequest.pairWithRouteExtras
  BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras
attribute [local irreducible]
  BinaryPromiseOpcodeRequest.rawWithControlExtras
  BinaryPromiseOpcodeRequest.parsedRawWithControlExtras
  BinaryPromiseOpcodeRequest.generatedWithControlExtras
  BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras
  BinaryPromiseOpcodeRequest.pairWithControlExtras
  BinaryPromiseOpcodeRequest.parsedPairWithControlExtras
theorem raw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let factoryReturned := BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits
    let returned := factoryReturned.1
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.raw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := raw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.rawWithFactoryExtras_compat,BinaryPromiseOpcodeRequest.rawWithControlExtras_compat,BinaryPromiseOpcodeRequest.rawWithRouteExtras_compat,BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.rawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.raw rich frame bits = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinarySamplerExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho



theorem parsedRaw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let factoryReturned := BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits
    let returned := factoryReturned.1
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedRaw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := parsedRaw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithControlExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedRaw rich frame bits = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinarySamplerExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinarySamplerExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho



theorem generated_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let factoryReturned := BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state
    let returned := factoryReturned.1
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.generated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := generated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.generatedWithFactoryExtras_compat,BinaryPromiseOpcodeRequest.generatedWithControlExtras_compat,BinaryPromiseOpcodeRequest.generatedWithRouteExtras_compat,BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.generatedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.generated next rich frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho



theorem parsedGenerated_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let factoryReturned := BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state
    let returned := factoryReturned.1
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedGenerated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := parsedGenerated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedGenerated next rich frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho



theorem pair_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let factoryReturned := BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state
    let returned := factoryReturned.1
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.pair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := pair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.pairWithFactoryExtras_compat,BinaryPromiseOpcodeRequest.pairWithControlExtras_compat,BinaryPromiseOpcodeRequest.pairWithRouteExtras_compat,BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.pairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.pair next frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2.1 + BinaryBigEndian.littleValue previous.1.1.1.1.2.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho



theorem parsedPair_complete_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let factoryReturned := BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state
    let returned := factoryReturned.1
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedPair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := parsedPair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithControlExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedPair next frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2.1 + BinaryBigEndian.littleValue previous.1.1.1.1.2.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho


end Blotto.BinaryReturnedFactoryExtras
