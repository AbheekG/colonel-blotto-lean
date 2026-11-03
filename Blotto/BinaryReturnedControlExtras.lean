import Blotto.BinaryReturnedRouteExtras

/-! Reached guard and root-probability normalization costs join the actual
route/draw/output fields. All old records and fields are exact projections.
Factory/resource normalization and complete native/physical models remain. -/
namespace Blotto.BinaryReturnedControlExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryCachedTerminalPreparation
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryTerminalCacheCertificate
open BinaryFactoryHeight BinaryExpressionCompiler
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryReturnedOutputExtras (join_source_component)
set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode BinaryNormalizedCoordinate.canonicalize

theorem canonical_bound (word : SignedWord) :
    (BinaryNormalizedCoordinate.canonicalize word).2 ≤155*(BinaryNormalizedCoordinate.canonicalize word).1.2 := by
  have hd := BinaryNormalizationPlan.canonicalize_division word
  have he := BinaryNormalizationPlan.canonicalize_price word
  have ht := BinaryResourceTraceLength.canonicalize_length word
  have hl := BinaryResourceTraceLength.canonicalize_work_lower word
  rw [← BinaryNormalizationPlan.canonicalize_compat] at ht hl
  unfold BinaryNormalizedCoordinate.canonicalize
  dsimp only
  omega

theorem root_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp).2 ≤155*(BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp).1.2 := by
  have h := canonical_bound input.p
  dsimp only [BinaryFourSmallCoinMeasured.sampleWithExtras]
  omega

theorem guard_bound (input : BinaryFourParameters.Input) :
    (BinaryFourGuardMeasured.guardWithExtras input).2 ≤155*(BinaryFourGuardMeasured.guardWithExtras input).1.2 := by
  have hFirst := BinaryNormalizationExtraWork.opcode_bound .sub Constant.one.word input.p
  have hSecond := BinaryNormalizationExtraWork.opcode_bound .mul
    (BinaryNormalizedCoordinate.opcode .sub Constant.one.word input.p).1.1.1 input.ell
  dsimp only [BinaryFourGuardMeasured.guardWithExtras]
  omega

theorem after_root_joint (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value)
    (extra : ℕ) (hRoot : extra ≤155*root.2) :
    (BinaryFourSmallMeasured.afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).2+extra ≤
      155*(BinaryFourSmallMeasured.afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).1.2 := by
  simp only [BinaryFourSmallMeasured.afterRootWithDrawExtras_record]
  cases h : root.1.1.1 with
  | none => dsimp only; omega
  | some branch =>
      cases branch
      · have h := BinaryReturnedReflectedExtras.run_bound store input hC hAd K outer scalar root.1.1.2 hNext
        dsimp only
        omega
      · have h := BinaryReturnedTerminalDrawExtras.small_uniform_bound store input hC hAd K scalar root.1.1.2 hNext
        dsimp only
        omega

theorem small_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourSmallMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).2 ≤155*(BinaryFourSmallMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.1.2 := by
  have hr := root_bound store input pc hp
  simp only [BinaryFourSmallMeasured.runWithControlExtras_record]
  exact after_root_joint store input hC hAd K outer scalar _ _ _ hr

theorem ordered_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourOrderedMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourOrderedMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).2 ≤155*(BinaryFourOrderedMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.1.2 := by
  have hg := guard_bound input
  simp only [BinaryFourOrderedMeasured.runWithControlExtras_record]
  split
  · rename_i hSelected
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hSelected
    have hd := BinaryReturnedTerminalDrawExtras.gluing_bound store input hC
      (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
    dsimp only [BinaryFourOrderedMeasured.join]
    omega
  · rename_i hSelected
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hSelected
    have hd := small_bound store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp
    dsimp only [BinaryFourOrderedMeasured.join]
    omega

theorem after_order_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourRestoredMeasured.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : BinaryFourRestoredMeasured.Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.afterOrderWithControlExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.2+(BinaryFourRestoredMeasured.afterOrderWithControlExtras store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤155*(BinaryFourRestoredMeasured.afterOrderWithControlExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.1.2 := by
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  have hd := ordered_bound store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  have hw := BinaryReturnedTerminalDrawExtras.restore_source_dominates store ordered
    (BinaryFourOrderedMeasured.runWithControlExtras store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp).1.1
  simp only [BinaryFourRestoredMeasured.afterOrderWithControlExtras_record]
  omega

theorem restored_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourRestoredMeasured.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourRestoredMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).2 ≤155*(BinaryFourRestoredMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.1.2 := by
  simp only [BinaryFourRestoredMeasured.runWithControlExtras_record]
  exact after_order_bound store input hC hAd _ _ K outer scalar pc hp

theorem mixed_three_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp).1.1.2+(BinaryWordGroupCompleteMeasured.mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp).1.1.1.2 := by
  let all := BinaryFourRestoredMeasured.runWithControlExtras store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  have hd := restored_bound store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp
  have he := BinaryReturnedRouteExtras.after_mixed_joint store routes pivot all.1.1 (all.1.2+all.2) hd
  dsimp only [all] at he
  simp only [BinaryWordGroupCompleteMeasured.mixedThreeRunWithControlExtras_record]
  omega

theorem draw_three_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.1.2+(BinaryWordTerminalCompleteMeasured.drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.1.1.2 := by
  subst m
  exact mixed_three_bound store input hC hAd routes pivot K outer scalar pc hp

theorem terminal_bound {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.runWithControlExtras store prepared hC hAd K outer scalar pc hp).1.1.2+(BinaryWordTerminalCompleteMeasured.runWithControlExtras store prepared hC hAd K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.runWithControlExtras store prepared hC hAd K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.runWithControlExtras store prepared hC hAd K outer scalar pc hp).1.1.1.2 := by
  simp only [BinaryWordTerminalCompleteMeasured.runWithControlExtras_record]
  split
  · rename_i hPivot
    have h := BinaryReturnedRouteExtras.uniform_bound store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
    dsimp only [BinaryWordTerminalCompleteMeasured.branch]
    omega
  · rename_i selected hPivot
    split
    · rename_i hTwo
      have h := BinaryReturnedRouteExtras.draw_two_bound store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
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
    (BinaryCacheContinuationCore.drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1.1.2+(BinaryCacheContinuationCore.drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1.2+(BinaryCacheContinuationCore.drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.drawWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.1.2 := by
  let request := parsed.1.2.logical.request
  let child := BinaryCacheContinuationCore.certified backend frame parsed hParsed seed rich
  let returned := child.1
  let observed := returned.1
  simp only [BinaryCacheContinuationCore.drawWithControlExtras_record]
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
    (BinaryCacheContinuationCore.fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1.1.2+(BinaryCacheContinuationCore.fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1.2+(BinaryCacheContinuationCore.fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.1.2 := by
  have h := draw_bound backend frame parsed hParsed seed rich K outer scalar
  simp only [BinaryCacheContinuationCore.fixedWithControlExtras_record]
  split <;> dsimp only <;> omega

theorem framed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((BinaryCacheContinuationCore.framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.2+(BinaryCacheContinuationCore.framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.2+(BinaryCacheContinuationCore.framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header).1.2+(BinaryCacheContinuationCore.framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header).2) ≤
      155*(BinaryCacheContinuationCore.framedWithControlExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.1.1.1.2 := by
  let controlled := BinaryCacheContinuationCore.fixedWithControlExtras backend frame parsed hParsed seed rich K outer scalar
  let all := controlled.1
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  have hd := fixed_bound backend frame parsed hParsed seed rich K outer scalar
  have ho := BinaryReturnedOutputExtras.output_bound parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  dsimp only [drawn,returned,child,supplied,all,controlled] at ho
  simp only [BinaryCacheContinuationCore.framedWithControlExtras_record]
  omega


theorem seed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    ((BinaryCacheContinuationCore.seedWithControlExtras backend frame parsed hParsed rich bits).1.1.1.2+(BinaryCacheContinuationCore.seedWithControlExtras backend frame parsed hParsed rich bits).1.1.2+(BinaryCacheContinuationCore.seedWithControlExtras backend frame parsed hParsed rich bits).1.2+(BinaryCacheContinuationCore.seedWithControlExtras backend frame parsed hParsed rich bits).2) ≤
      155*(BinaryCacheContinuationCore.seedWithControlExtras backend frame parsed hParsed rich bits).1.1.1.1.1.1.2 := by
  simp only [BinaryCacheContinuationCore.seedWithControlExtras_record]
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
    ((BinaryCacheFinishRequest.seedWithControlExtras frame parsed hParsed rich bits).1.1.1.2+(BinaryCacheFinishRequest.seedWithControlExtras frame parsed hParsed rich bits).1.1.2+(BinaryCacheFinishRequest.seedWithControlExtras frame parsed hParsed rich bits).1.2+(BinaryCacheFinishRequest.seedWithControlExtras frame parsed hParsed rich bits).2) ≤
      155*(BinaryCacheFinishRequest.seedWithControlExtras frame parsed hParsed rich bits).1.1.1.1.1.1.2 :=
  seed_bound BinaryCacheFinishRequest.backend frame parsed hParsed rich bits

theorem parser_raw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    ((BinaryRawParserContinuation.rawWithControlExtras backend rich frame bits).1.1.1.2+(BinaryRawParserContinuation.rawWithControlExtras backend rich frame bits).1.1.2+(BinaryRawParserContinuation.rawWithControlExtras backend rich frame bits).1.2+(BinaryRawParserContinuation.rawWithControlExtras backend rich frame bits).2) ≤ 155*(BinaryRawParserContinuation.rawWithControlExtras backend rich frame bits).1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.rawWithControlExtras_record]
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
    ((BinaryRawParserContinuation.parsedRawWithControlExtras backend rich frame bits).1.1.1.2+(BinaryRawParserContinuation.parsedRawWithControlExtras backend rich frame bits).1.1.2+(BinaryRawParserContinuation.parsedRawWithControlExtras backend rich frame bits).1.2+(BinaryRawParserContinuation.parsedRawWithControlExtras backend rich frame bits).2) ≤ 155*(BinaryRawParserContinuation.parsedRawWithControlExtras backend rich frame bits).1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedRawWithControlExtras_record]
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
    ((BinaryRawParserContinuation.generatedWithControlExtras backend next rich frame state).1.1.1.2+(BinaryRawParserContinuation.generatedWithControlExtras backend next rich frame state).1.1.2+(BinaryRawParserContinuation.generatedWithControlExtras backend next rich frame state).1.2+(BinaryRawParserContinuation.generatedWithControlExtras backend next rich frame state).2) ≤ 155*(BinaryRawParserContinuation.generatedWithControlExtras backend next rich frame state).1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.generatedWithControlExtras_record]
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
    ((BinaryRawParserContinuation.parsedGeneratedWithControlExtras backend next rich frame state).1.1.1.2+(BinaryRawParserContinuation.parsedGeneratedWithControlExtras backend next rich frame state).1.1.2+(BinaryRawParserContinuation.parsedGeneratedWithControlExtras backend next rich frame state).1.2+(BinaryRawParserContinuation.parsedGeneratedWithControlExtras backend next rich frame state).2) ≤ 155*(BinaryRawParserContinuation.parsedGeneratedWithControlExtras backend next rich frame state).1.1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedGeneratedWithControlExtras_record]
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
    ((BinaryRawParserContinuation.pairWithControlExtras backend next frame state).1.1.1.2+(BinaryRawParserContinuation.pairWithControlExtras backend next frame state).1.1.2+(BinaryRawParserContinuation.pairWithControlExtras backend next frame state).1.2+(BinaryRawParserContinuation.pairWithControlExtras backend next frame state).2) ≤ 155*(BinaryRawParserContinuation.pairWithControlExtras backend next frame state).1.1.1.1.1.1.2 := by
  let first := BinaryRawParserContinuation.generatedWithControlExtras backend next true frame state
  let rich := first.1.1.1.1.1
  have hFirst := parser_generated_bound backend next true frame state
  have hSecond := parser_generated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.pairWithControlExtras_record]
  omega

theorem parser_parsedPair_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryRawParserContinuation.parsedPairWithControlExtras backend next frame state).1.1.1.2+(BinaryRawParserContinuation.parsedPairWithControlExtras backend next frame state).1.1.2+(BinaryRawParserContinuation.parsedPairWithControlExtras backend next frame state).1.2+(BinaryRawParserContinuation.parsedPairWithControlExtras backend next frame state).2) ≤ 155*(BinaryRawParserContinuation.parsedPairWithControlExtras backend next frame state).1.1.1.1.1.1.2 := by
  let first := BinaryRawParserContinuation.parsedGeneratedWithControlExtras backend next true frame state
  let rich := first.1.1.1.1.1
  have hFirst := parser_parsedGenerated_bound backend next true frame state
  have hSecond := parser_parsedGenerated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.parsedPairWithControlExtras_record]
  omega

theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits).1.1.1.2+(BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits).1.1.2+(BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits).1.2+(BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits).2) ≤ 155*(BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits).1.1.1.1.1.1.2 :=
  parser_raw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits).1.1.1.2+(BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits).1.1.2+(BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits).1.2+(BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits).1.1.1.1.1.1.2 :=
  parser_parsedRaw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state).1.1.2+(BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state).1.2+(BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state).1.1.1.1.1.1.2 :=
  parser_generated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state).1.1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state).1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state).1.1.1.1.1.1.2 :=
  parser_parsedGenerated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem pair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state).1.1.2+(BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state).1.2+(BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state).1.1.1.1.1.1.2 :=
  parser_pair_bound BinaryPromiseOpcodeRequest.backend next frame state

theorem parsedPair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state).1.1.1.2+(BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state).1.1.2+(BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state).1.2+(BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state).1.1.1.1.1.1.2 :=
  parser_parsedPair_bound BinaryPromiseOpcodeRequest.backend next frame state

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
    let returned := BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.raw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := raw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.rawWithControlExtras_compat,BinaryPromiseOpcodeRequest.rawWithRouteExtras_compat,BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.rawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedRaw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := parsedRaw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedRawWithControlExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.generated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := generated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.generatedWithControlExtras_compat,BinaryPromiseOpcodeRequest.generatedWithRouteExtras_compat,BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.generatedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedGenerated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := parsedGenerated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.pair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := pair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.pairWithControlExtras_compat,BinaryPromiseOpcodeRequest.pairWithRouteExtras_compat,BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.pairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state
    let produced := returned.1.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedPair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := parsedPair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedPairWithControlExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedPair next frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2.1 + BinaryBigEndian.littleValue previous.1.1.1.1.2.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho

theorem canonical_price (word : SignedWord) :
    (BinaryNormalizedCoordinate.canonicalize word).1.2+(BinaryNormalizedCoordinate.canonicalize word).2 ≤
      156*(600*(width word+1)^2) := by
  have he := canonical_bound word
  have hw := BinaryQuadraticNormalization.canonicalizeWithWork_bound word
  rw [← BinaryQuadraticMeasured.canonicalize_work] at hw
  simp only [BinaryNormalizedCoordinate.canonicalize_record] at he ⊢
  omega

theorem root_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp).1.2+(BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp).2 ≤156*(BinaryFourSmallCoinMeasured.workEnvelope s store.width (store.cap.value-pc.value)) := by
  have he := root_bound store input pc hp
  have hw := BinaryFourSmallCoinMeasured.sample_work store input source hC hR s hH pc hp
  simp only [BinaryFourSmallCoinMeasured.sampleWithExtras_compat] at he ⊢
  omega

theorem guard_price (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : BinaryFourNativeOrderWork.InputHeight input s) :
    (BinaryFourGuardMeasured.guardWithExtras input).1.2+(BinaryFourGuardMeasured.guardWithExtras input).2 ≤156*(BinaryFourGuardMeasured.workEnvelope s) := by
  have he := guard_bound input
  have hw := BinaryFourGuardMeasured.guard_work input hC s hs hHeight
  simp only [BinaryFourGuardMeasured.guardWithExtras_compat] at he ⊢
  omega

theorem small_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.1.2+(BinaryFourSmallMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourSmallMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).2 ≤156*(BinaryFourSmallMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := small_bound store input hC hAd K outer scalar pc hp
  have hw := (BinaryFourSmallMeasured.run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp).1
  simp only [BinaryFourSmallMeasured.runWithControlExtras_compat,BinaryFourSmallMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem ordered_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourOrderedMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.1.2+(BinaryFourOrderedMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourOrderedMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).2 ≤156*(BinaryFourOrderedMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := ordered_bound store input hC hAd K outer scalar pc hp
  have hw := (BinaryFourOrderedMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp).1
  simp only [BinaryFourOrderedMeasured.runWithControlExtras_compat,BinaryFourOrderedMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem restored_price (store : BinarySeedLookupTree.Store) (input : BinaryFourRestoredMeasured.Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.1.2+(BinaryFourRestoredMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourRestoredMeasured.runWithControlExtras store input hC hAd K outer scalar pc hp).2 ≤156*(BinaryFourRestoredMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := restored_bound store input hC hAd K outer scalar pc hp
  have hw := (BinaryFourRestoredMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp).1
  simp only [BinaryFourRestoredMeasured.runWithControlExtras_compat,BinaryFourRestoredMeasured.runWithDrawExtras_compat] at he ⊢
  omega

end Blotto.BinaryReturnedControlExtras
