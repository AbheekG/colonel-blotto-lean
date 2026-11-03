import Blotto.BinaryReturnedCompleteDrawOutputExtras

/-! Actual route multiplications and the mixed pivot addition are collected
once and joined with preceding draw/output fields. Entire prior records and
cost fields are retained. Other normalization and native/physical costs remain. -/
namespace Blotto.BinaryReturnedRouteExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryCachedTerminalPreparation
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryTerminalCacheCertificate
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryReturnedOutputExtras (join_source_component)
set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode

theorem cell_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) :
    (BinaryGroupEmissionMeasured.cellWithExtras routes row j).2 ≤155*(BinaryGroupEmissionMeasured.cellWithExtras routes row j).1.2 := by
  dsimp only [BinaryGroupEmissionMeasured.cellWithExtras]
  split
  · dsimp only; omega
  · rename_i g hRoute
    have h := BinaryNormalizationExtraWork.opcode_bound .mul (routes.read j).2 (row.read g)
    dsimp only
    omega

theorem emit_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    (BinaryGroupEmissionMeasured.emitWithExtras routes row).2 ≤155*(BinaryGroupEmissionMeasured.emitWithExtras routes row).1.2 := by
  exact BinaryLifetimeArrayExtras.build_bound n (BinaryGroupEmissionMeasured.cellWithExtras routes row) 155
    (fun j => cell_bound routes row j)

theorem mixed_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) :
    (BinaryGroupEmissionMeasured.emitMixedWithExtras routes pivot row).2 ≤155*(BinaryGroupEmissionMeasured.emitMixedWithExtras routes pivot row).1.2 := by
  have he := emit_bound routes (BinaryGroupEmissionMeasured.subrow row).1.1
  have ha := BinaryNormalizationExtraWork.opcode_bound .add
    ((BinaryGroupEmissionMeasured.emitWithExtras routes (BinaryGroupEmissionMeasured.subrow row).1.1).1.1.1.read pivot) (row.read (Fin.last m))
  dsimp only [BinaryGroupEmissionMeasured.emitMixedWithExtras]
  omega

theorem option_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (rows : Option (FixedArrayTable m SignedWord)) :
    (BinaryGroupEmissionMeasured.emitOptionWithExtras routes rows).2 ≤155*(BinaryGroupEmissionMeasured.emitOptionWithExtras routes rows).1.2 := by
  cases rows with
  | none => dsimp only [BinaryGroupEmissionMeasured.emitOptionWithExtras]; omega
  | some row =>
      have h := emit_bound routes row
      dsimp only [BinaryGroupEmissionMeasured.emitOptionWithExtras]
      omega

theorem mixed_option_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    (BinaryGroupEmissionMeasured.emitMixedOptionWithExtras routes pivot rows).2 ≤155*(BinaryGroupEmissionMeasured.emitMixedOptionWithExtras routes pivot rows).1.2 := by
  cases rows with
  | none => dsimp only [BinaryGroupEmissionMeasured.emitMixedOptionWithExtras]; omega
  | some row =>
      have h := mixed_bound routes pivot row
      dsimp only [BinaryGroupEmissionMeasured.emitMixedOptionWithExtras]
      omega

theorem emit_extra {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    (BinaryGroupEmissionMeasured.emitWithExtras routes row).2 =
      ∑ j, (BinaryGroupEmissionMeasured.cellWithExtras routes row j).2 :=
  BinaryLifetimeArrayExtras.build_extra n (BinaryGroupEmissionMeasured.cellWithExtras routes row)

theorem cell_price {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) (W : ℕ)
    (hRoutes : ∀ j,width (routes.read j).2 ≤ W) (hRows : ∀ g,width (row.read g) ≤ W) :
    (BinaryGroupEmissionMeasured.cellWithExtras routes row j).1.2+(BinaryGroupEmissionMeasured.cellWithExtras routes row j).2 ≤156*(11000*(W+1)^2+8) := by
  have he := cell_bound routes row j
  have hw := BinaryGroupEmissionMeasured.cell_work routes row j W hRoutes hRows
  simp only [BinaryGroupEmissionMeasured.cellWithExtras_compat] at he ⊢
  omega

theorem emit_price {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (W : ℕ)
    (hRoutes : ∀ j,width (routes.read j).2 ≤ W) (hRows : ∀ g,width (row.read g) ≤ W) :
    (BinaryGroupEmissionMeasured.emitWithExtras routes row).1.2+(BinaryGroupEmissionMeasured.emitWithExtras routes row).2 ≤156*(BinaryGroupEmissionMeasured.workEnvelope n W) := by
  have he := emit_bound routes row
  have hw := BinaryGroupEmissionMeasured.emit_work routes row W hRoutes hRows
  simp only [BinaryGroupEmissionMeasured.emitWithExtras_compat] at he ⊢
  omega

theorem mixed_price {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ g,RationalHeight (value (row.read g)) s) :
    (BinaryGroupEmissionMeasured.emitMixedWithExtras routes pivot row).1.2+(BinaryGroupEmissionMeasured.emitMixedWithExtras routes pivot row).2 ≤156*(BinaryGroupEmissionMeasured.mixedWorkEnvelope n m s) := by
  have he := mixed_bound routes pivot row
  have hw := BinaryGroupEmissionMeasured.emitMixed_work routes pivot row hRoutes hRows s hs hR hH
  simp only [BinaryGroupEmissionMeasured.emitMixedWithExtras_compat] at he ⊢
  omega

theorem option_price {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) (W : ℕ)
    (hR : ∀ j,width (routes.read j).2 ≤ W)
    (hH : ∀ row,rows = some row → ∀ g,width (row.read g) ≤ W) :
    (BinaryGroupEmissionMeasured.emitOptionWithExtras routes rows).1.2+(BinaryGroupEmissionMeasured.emitOptionWithExtras routes rows).2 ≤156*(BinaryGroupEmissionMeasured.workEnvelope n W+4) := by
  have he := option_bound routes rows
  have hw := BinaryGroupEmissionMeasured.emitOption_work routes rows W hR hH
  simp only [BinaryGroupEmissionMeasured.emitOptionWithExtras_compat] at he ⊢
  omega

theorem mixed_option_price {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ row,rows = some row → ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ row,rows = some row → ∀ g,RationalHeight (value (row.read g)) s) :
    (BinaryGroupEmissionMeasured.emitMixedOptionWithExtras routes pivot rows).1.2+(BinaryGroupEmissionMeasured.emitMixedOptionWithExtras routes pivot rows).2 ≤156*(BinaryGroupEmissionMeasured.mixedWorkEnvelope n m s+4) := by
  have he := mixed_option_bound routes pivot rows
  have hw := BinaryGroupEmissionMeasured.emitMixedOption_work routes pivot rows hRoutes hRows s hs hR hH
  simp only [BinaryGroupEmissionMeasured.emitMixedOptionWithExtras_compat] at he ⊢
  omega

theorem after_mixed_joint {n m : ℕ} (store : BinarySeedLookupTree.Store) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ) (extra : ℕ) (hDraw : extra ≤155*drawn.2) :
    extra+(BinaryWordGroupCompleteMeasured.afterMixedWithRouteExtras store routes pivot drawn).2 ≤
      155*(BinaryWordGroupCompleteMeasured.afterMixedWithRouteExtras store routes pivot drawn).1.2 := by
  have h := mixed_option_bound routes pivot drawn.1.1.1
  dsimp only [BinaryWordGroupCompleteMeasured.afterMixedWithRouteExtras,BinaryWordGroupCompleteMeasured.collect]
  omega

theorem after_mixed_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ) :
    (BinaryWordGroupCompleteMeasured.afterMixedWithRouteExtras store routes pivot drawn).2 ≤155*(BinaryWordGroupCompleteMeasured.afterMixedWithRouteExtras store routes pivot drawn).1.2 := by
  simpa only [Nat.zero_add] using after_mixed_joint store routes pivot drawn 0 (Nat.zero_le _)

theorem uniform_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.uniformRunWithRouteExtras store input hC hAd hm routes K scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.uniformRunWithRouteExtras store input hC hAd hm routes K scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.uniformRunWithRouteExtras store input hC hAd hm routes K scalar pc hp).1.1.2 := by
  let produced := BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp
  have hd := BinaryReturnedCategoricalExtras.uniform_draw_bound store input hC hAd hm K scalar pc hp
  have he := option_bound routes produced.1.1.1.1
  dsimp only [produced] at he
  simp only [BinaryWordGroupCompleteMeasured.uniformRunWithRouteExtras_record,BinaryWordGroupCompleteMeasured.collect]
  omega

theorem mixed_two_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp).1.1.2 := by
  have hd := BinaryReturnedCategoricalExtras.mixed_draw_bound store input hC hAd K scalar pc hp
  have h := after_mixed_joint store routes pivot (BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).1 (BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).2 hd
  simp only [BinaryWordGroupCompleteMeasured.mixedTwoRunWithRouteExtras_record]
  exact h

theorem mixed_three_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordGroupCompleteMeasured.mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp).1.1.2 := by
  have hd := BinaryReturnedTerminalDrawExtras.restored_bound store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp
  have h := after_mixed_joint store routes pivot (BinaryFourRestoredMeasured.runWithDrawExtras store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp).1 (BinaryFourRestoredMeasured.runWithDrawExtras store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp).2 hd
  simp only [BinaryWordGroupCompleteMeasured.mixedThreeRunWithRouteExtras_record]
  exact h

theorem draw_two_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawTwoWithRouteExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.drawTwoWithRouteExtras store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.drawTwoWithRouteExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.1.2 := by
  subst m
  exact mixed_two_bound store input hC hAd routes pivot K scalar pc hp

theorem draw_three_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawThreeWithRouteExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.drawThreeWithRouteExtras store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.drawThreeWithRouteExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.1.2 := by
  subst m
  exact mixed_three_bound store input hC hAd routes pivot K outer scalar pc hp

theorem terminal_bound {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.runWithRouteExtras store prepared hC hAd K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.runWithRouteExtras store prepared hC hAd K outer scalar pc hp).2 ≤155*(BinaryWordTerminalCompleteMeasured.runWithRouteExtras store prepared hC hAd K outer scalar pc hp).1.1.2 := by
  simp only [BinaryWordTerminalCompleteMeasured.runWithRouteExtras_record]
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
    (BinaryCacheContinuationCore.drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1.2+(BinaryCacheContinuationCore.drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.drawWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.2 := by
  let request := parsed.1.2.logical.request
  let child := BinaryCacheContinuationCore.certified backend frame parsed hParsed seed rich
  let returned := child.1
  let observed := returned.1
  simp only [BinaryCacheContinuationCore.drawWithRouteExtras_record]
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
    (BinaryCacheContinuationCore.fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1.2+(BinaryCacheContinuationCore.fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).2 ≤155*(BinaryCacheContinuationCore.fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar).1.1.1.1.2 := by
  have h := draw_bound backend frame parsed hParsed seed rich K outer scalar
  simp only [BinaryCacheContinuationCore.fixedWithRouteExtras_record]
  split <;> dsimp only <;> omega

theorem framed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((BinaryCacheContinuationCore.framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.2+(BinaryCacheContinuationCore.framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header).1.2+(BinaryCacheContinuationCore.framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header).2) ≤
      155*(BinaryCacheContinuationCore.framedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar header).1.1.1.1.1.2 := by
  let all := BinaryCacheContinuationCore.fixedWithRouteExtras backend frame parsed hParsed seed rich K outer scalar
  let supplied := all.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1
  have hd := fixed_bound backend frame parsed hParsed seed rich K outer scalar
  have ho := BinaryReturnedOutputExtras.output_bound parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  dsimp only [drawn,returned,child,supplied,all] at ho
  simp only [BinaryCacheContinuationCore.framedWithRouteExtras_record]
  omega


theorem seed_bound {E : Type*} [Zero E] [Add E] (backend : BinaryCacheContinuationCore.Backend E)
    (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (bits : List Bool) :
    ((BinaryCacheContinuationCore.seedWithRouteExtras backend frame parsed hParsed rich bits).1.1.2+(BinaryCacheContinuationCore.seedWithRouteExtras backend frame parsed hParsed rich bits).1.2+(BinaryCacheContinuationCore.seedWithRouteExtras backend frame parsed hParsed rich bits).2) ≤
      155*(BinaryCacheContinuationCore.seedWithRouteExtras backend frame parsed hParsed rich bits).1.1.1.1.1.2 := by
  simp only [BinaryCacheContinuationCore.seedWithRouteExtras_record]
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
    ((BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hParsed rich bits).1.1.2+(BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hParsed rich bits).1.2+(BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hParsed rich bits).2) ≤
      155*(BinaryCacheFinishRequest.seedWithRouteExtras frame parsed hParsed rich bits).1.1.1.1.1.2 :=
  seed_bound BinaryCacheFinishRequest.backend frame parsed hParsed rich bits

theorem parser_raw_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E) (rich : Bool) (frame bits : List Bool) :
    ((BinaryRawParserContinuation.rawWithRouteExtras backend rich frame bits).1.1.2+(BinaryRawParserContinuation.rawWithRouteExtras backend rich frame bits).1.2+(BinaryRawParserContinuation.rawWithRouteExtras backend rich frame bits).2) ≤ 155*(BinaryRawParserContinuation.rawWithRouteExtras backend rich frame bits).1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.rawWithRouteExtras_record]
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
    ((BinaryRawParserContinuation.parsedRawWithRouteExtras backend rich frame bits).1.1.2+(BinaryRawParserContinuation.parsedRawWithRouteExtras backend rich frame bits).1.2+(BinaryRawParserContinuation.parsedRawWithRouteExtras backend rich frame bits).2) ≤ 155*(BinaryRawParserContinuation.parsedRawWithRouteExtras backend rich frame bits).1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedRawWithRouteExtras_record]
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
    ((BinaryRawParserContinuation.generatedWithRouteExtras backend next rich frame state).1.1.2+(BinaryRawParserContinuation.generatedWithRouteExtras backend next rich frame state).1.2+(BinaryRawParserContinuation.generatedWithRouteExtras backend next rich frame state).2) ≤ 155*(BinaryRawParserContinuation.generatedWithRouteExtras backend next rich frame state).1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.generatedWithRouteExtras_record]
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
    ((BinaryRawParserContinuation.parsedGeneratedWithRouteExtras backend next rich frame state).1.1.2+(BinaryRawParserContinuation.parsedGeneratedWithRouteExtras backend next rich frame state).1.2+(BinaryRawParserContinuation.parsedGeneratedWithRouteExtras backend next rich frame state).2) ≤ 155*(BinaryRawParserContinuation.parsedGeneratedWithRouteExtras backend next rich frame state).1.1.1.1.1.2 := by
  simp only [BinaryRawParserContinuation.parsedGeneratedWithRouteExtras_record]
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
    ((BinaryRawParserContinuation.pairWithRouteExtras backend next frame state).1.1.2+(BinaryRawParserContinuation.pairWithRouteExtras backend next frame state).1.2+(BinaryRawParserContinuation.pairWithRouteExtras backend next frame state).2) ≤ 155*(BinaryRawParserContinuation.pairWithRouteExtras backend next frame state).1.1.1.1.1.2 := by
  let first := BinaryRawParserContinuation.generatedWithRouteExtras backend next true frame state
  let rich := first.1.1.1.1
  have hFirst := parser_generated_bound backend next true frame state
  have hSecond := parser_generated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.pairWithRouteExtras_record]
  omega

theorem parser_parsedPair_bound {E : Type*} [Zero E] [Add E] (backend : BinaryRawParserContinuation.Backend E)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryRawParserContinuation.parsedPairWithRouteExtras backend next frame state).1.1.2+(BinaryRawParserContinuation.parsedPairWithRouteExtras backend next frame state).1.2+(BinaryRawParserContinuation.parsedPairWithRouteExtras backend next frame state).2) ≤ 155*(BinaryRawParserContinuation.parsedPairWithRouteExtras backend next frame state).1.1.1.1.1.2 := by
  let first := BinaryRawParserContinuation.parsedGeneratedWithRouteExtras backend next true frame state
  let rich := first.1.1.1.1
  have hFirst := parser_parsedGenerated_bound backend next true frame state
  have hSecond := parser_parsedGenerated_bound backend next false frame rich.1.1.1.1.2
  dsimp only [rich,first] at hSecond
  simp only [BinaryRawParserContinuation.parsedPairWithRouteExtras_record]
  omega

theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits).1.1.2+(BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits).1.2+(BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits).2) ≤ 155*(BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits).1.1.1.1.1.2 :=
  parser_raw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    ((BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits).1.1.2+(BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits).1.2+(BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits).1.1.1.1.1.2 :=
  parser_parsedRaw_bound BinaryPromiseOpcodeRequest.backend rich frame bits

theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state).1.1.2+(BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state).1.2+(BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state).1.1.1.1.1.2 :=
  parser_generated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state).1.1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state).1.2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state).1.1.1.1.1.2 :=
  parser_parsedGenerated_bound BinaryPromiseOpcodeRequest.backend next rich frame state

theorem pair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state).1.1.2+(BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state).1.2+(BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state).1.1.1.1.1.2 :=
  parser_pair_bound BinaryPromiseOpcodeRequest.backend next frame state

theorem parsedPair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state).1.1.2+(BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state).1.2+(BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state).2) ≤ 155*(BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state).1.1.1.1.1.2 :=
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
theorem raw_complete_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    let returned := BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits
    let produced := returned.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.raw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := raw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.rawWithRouteExtras_compat,BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.rawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.rawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithDrawOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.rawWithRouteExtras rich frame bits).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits
    let produced := returned.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.rawCost rich frame bits+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinarySamplerExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedRaw_complete_joint
  refine ⟨156*C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have he := parsedRaw_bound rich frame bits
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedRawWithOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithDrawOutputExtras rich frame bits).2+(BinaryPromiseOpcodeRequest.parsedRawWithRouteExtras rich frame bits).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state
    let produced := returned.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.generated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := generated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.generatedWithRouteExtras_compat,BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.generatedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.generatedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithDrawOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.generatedWithRouteExtras next rich frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state
    let produced := returned.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.generatedCost next rich frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedGenerated_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have he := parsedGenerated_bound next rich frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedGeneratedWithOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithDrawOutputExtras next rich frame state).2+(BinaryPromiseOpcodeRequest.parsedGeneratedWithRouteExtras next rich frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state
    let produced := returned.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.pairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.pair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := pair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.pairWithRouteExtras_compat,BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.pairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.pairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithDrawOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.pairWithRouteExtras next frame state).2 = extra at he ⊢
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
    let returned := BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state
    let produced := returned.1.1.1
    (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.2+returned.1.2+returned.2) ≤ C*(frame.length+1)^d ∧
      binaryWordWidth (returned.1.1.2+returned.1.2+returned.2) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,hOld⟩ := BinaryCompleteRequestArithmeticEntryWork.parsedPair_complete_joint
  refine ⟨156*C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have he := parsedPair_bound next frame state
  dsimp only at ho ⊢
  simp only [BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras_compat,BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras_compat,Nat.mul_assoc] at he ⊢
  generalize (BinaryPromiseOpcodeRequest.parsedPairWithOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithDrawOutputExtras next frame state).2+(BinaryPromiseOpcodeRequest.parsedPairWithRouteExtras next frame state).2 = extra at he ⊢
  generalize BinaryPromiseOpcodeRequest.parsedPair next frame state = previous at ho he ⊢
  have hSource : previous.1.1.2 ≤ BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2 := by
    simpa only [Nat.add_assoc] using
      (Nat.le_add_left previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state)).trans
        (Nat.le_add_right (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2) (BinaryBigEndian.littleValue previous.1.1.1.1.2.1 + BinaryBigEndian.littleValue previous.1.1.1.1.2.2 + usage previous.1.1.1.2 + 
      BinaryGenerationExecutionCharges.total previous.1.2 + previous.2.1.1 + previous.2.1.2 + previous.2.2.1.1.1.1.1.1.1.1.1.1 + previous.2.2.1.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.1.2 + previous.2.2.1.1.1.1.1.2 + previous.2.2.1.1.1.1.2 + previous.2.2.1.1.1.2 + previous.2.2.1.1.2 + previous.2.2.1.2 + previous.2.2.2.1.1.1.1.1.1 + previous.2.2.2.1.1.1.1.1.2 + previous.2.2.2.1.1.1.1.2 + previous.2.2.2.1.1.1.2 + previous.2.2.2.1.1.2 + previous.2.2.2.1.2 + previous.2.2.2.2))
  exact join_source_component previous.1.1.2 (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost next frame state+previous.1.1.2+BinaryBigEndian.littleValue previous.1.1.1.1.2.1+BinaryBigEndian.littleValue previous.1.1.1.1.2.2+usage previous.1.1.1.2+
      BinaryGenerationExecutionCharges.total previous.1.2+previous.2.1.1+previous.2.1.2+previous.2.2.1.1.1.1.1.1.1.1.1.1+previous.2.2.1.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.1.2+previous.2.2.1.1.1.1.1.2+previous.2.2.1.1.1.1.2+previous.2.2.1.1.1.2+previous.2.2.1.1.2+previous.2.2.1.2+previous.2.2.2.1.1.1.1.1.1+previous.2.2.2.1.1.1.1.1.2+previous.2.2.2.1.1.1.1.2+previous.2.2.2.1.1.1.2+previous.2.2.2.1.1.2+previous.2.2.2.1.2+previous.2.2.2.2) extra (C*(frame.length+1)^d) hSource he ho

end Blotto.BinaryReturnedRouteExtras
