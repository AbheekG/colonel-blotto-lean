import Blotto.GeneralPaperUnitCallerSharpWork

/-! Genuine native selected compiler-pair work under sharp operand and
trajectory bounds. Existing native branch/strict/endpoint prices remain
unchanged; their complete arithmetic cost is bounded here. -/
namespace Blotto.GeneralPaperCompilerSharpWork
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra GeneralPaperNativeSourceRates
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def bitRate (x : Input) : ℕ := monomial 5 0 4 x+GeneralPaperSourceCallerSharpWork.bitRate x

theorem embed {f : Input → ℕ} {a c : ℕ} (h : Rated f a 0 c)
    (fits : (a≤5 ∧ c≤4) ∨ (a≤4 ∧ c≤5) ∨ (a≤3 ∧ c≤6)) : Soft bitRate f := by
  rcases fits with h0|h1|h2
  · apply rate_mono (weaken h h0.1 le_rfl h0.2)
    intro x
    unfold bitRate
    omega
  · apply rate_mono (weaken h h1.1 le_rfl h1.2)
    intro x
    unfold bitRate GeneralPaperSourceCallerSharpWork.bitRate
    omega
  · apply rate_mono (weaken h h2.1 le_rfl h2.2)
    intro x
    unfold bitRate GeneralPaperSourceCallerSharpWork.bitRate
    omega

open Lean Meta Elab Tactic in
elab "source_time" : tactic => withMainContext do
  let main ← getMainGoal
  let target ← instantiateMVars (← main.getType)
  unless target.isAppOf ``GeneralPaperSourceSoftBounds.Soft do
    throwError "source_time expects a Soft goal, saw {target.getAppFn}"
  let fn := target.getAppArgs[1]!
  lambdaTelescope fn fun xs body => do
    unless xs.size == 1 do throwError "source_time expects one input"
    let x := xs[0]!
    let close := fun e => mkLambdaFVars #[x] e
    let rec build : Nat → Expr → TacticM Expr
      | 0,_ => throwError "source_time structural depth exceeded"
      | fuel+1,e => do
        let e ← instantiateMVars e
        let name := e.getAppFn.constName?
        let args := e.getAppArgs
        if name == some ``HAdd.hAdd || name == some ``Nat.add then
          let p ← build fuel args[args.size-2]!
          let q ← build fuel args.back!
          return ← mkAppM ``GeneralPaperSourceSoftBounds.add_same #[p,q]
        let f ← close e
        let a ← mkFreshExprMVar (mkConst ``Nat)
        let b ← mkFreshExprMVar (mkConst ``Nat)
        let c ← mkFreshExprMVar (mkConst ``Nat)
        let ty ← mkAppM ``GeneralPaperSourceRateAlgebra.Rated #[f,a,b,c]
        let g ← mkFreshExprMVar ty
        let old ← getGoals
        setGoals [g.mvarId!]
        try
          evalTactic (← `(tactic| source_space))
          unless (← getGoals).isEmpty do throwError "unclosed source_time summand"
          let some av ← getNatValue? (← whnf (← instantiateMVars a)) | throwError "nonliteral field degree"
          let some bv ← getNatValue? (← whnf (← instantiateMVars b)) | throwError "nonliteral alphabet degree"
          let some cv ← getNatValue? (← whnf (← instantiateMVars c)) | throwError "nonliteral accuracy degree"
          unless bv == 0 && ((av ≤ 5 && cv ≤ 4) || (av ≤ 4 && cv ≤ 5) || (av ≤ 3 && cv ≤ 6)) do
            throwError "source_time summand has degrees ({av},{bv},{cv}): {e}"
          let proof ← instantiateMVars g
          let embedded ← mkAppM ``Blotto.GeneralPaperCompilerSharpWork.embed #[proof]
          let ty ← whnf (← inferType embedded)
          let .forallE _ fitType _ _ := ty | throwError "source_time missing degree condition"
          let fit ← mkFreshExprMVar fitType
          setGoals [fit.mvarId!]
          evalTactic (← `(tactic| decide))
          return ← instantiateMVars (mkApp embedded fit)
        finally
          setGoals old
    let proof ← build 512 body
    main.assign proof
    replaceMainGoal []

theorem price_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft bitRate
    (fun x => GeneralPaperSourceCompilerPairStorageRates.price (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hsA := GeneralPaperScoreStorageRates.anchor_small
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  have hH := GeneralPaperBasisStorageRates.determinant_length
  have hMeasure := GeneralPaperSourceEndpointFractionConstructionStorageRates.classifier_measure_sharp
  have hGridWord := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  have hsMeasure := GeneralPaperSourceStorageRates.precall_measure_small
  dsimp only [GeneralPaperSourceCompilerPairStorageRates.sourceProfile,GeneralPaperSourceCompilerPairStorageRates.endpointPrice,GeneralPaperRetainedCompilerPairStorage.profile,
    GeneralPaperRetainedCompilerPairStorage.pairProfile,GeneralPaperRetainedCompilerPairStorage.price,GeneralPaperRetainedCompilerPairStorage.metadataCap,
    GeneralPaperSourceModifiedColumnStorageRates.price,GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth,GeneralPaperClassifierResultStorage.profile,
    GeneralPaperPrecallCacheStorage.payload,GeneralPaperSelectionPoints.width,GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperSourceCompilerBranchStorageRates.price,GeneralPaperSourceUnitCallerStorageRates.operandWidth,GeneralPaperEncodedRationalRows.rowProfile,
    GeneralPaperNativeEndpointColumnsStorage.profile,GeneralPaperRetainedCompilerBranchStorage.price,GeneralPaperRetainedModifiedColumnStorage.metadataCap,
    GeneralPaperSourceCompilerBranchStorageRates.tagPrice,GeneralPaperSourceCompilerBranchStorageRates.testPrice,GeneralPaperSourceOuterEndpointStorageRates.price,
    GeneralPaperSourceStrictPreparationBits.profile,GeneralPaperEnclosingSourceOwners.columnsProfile,GeneralPaperNativeEndpointColumnsStorage.fieldProfile,
    GeneralPaperNativeEndpointColumnsStorage.metadataCap,GeneralPaperRetainedModifiedColumnStorage.price,GeneralPaperRetainedTransferPrice.bitProfile,
    GeneralPaperSourceBasisControllerStorageRates.workPrice,GeneralPaperSourceEndpointContinuationReturnBounds.price,GeneralPaperSourceEndpointScalarStorageRates.operandWidth,
    GeneralPaperSourceInitializerReturnStorageRates.inputPrice,GeneralPaperBasisControllerBits.profile,GeneralPaperEnclosingSourceOwners.columnProfile,
    GeneralPaperNativeEndpointAnchorStorage.profile,GeneralPaperNativeEndpointColumnsStorage.fieldCap,GeneralPaperNativeEndpointColumnsStorage.price,
    GeneralPaperNativePayloadFillStorage.profile,GeneralPaperRawEndpointReturnStorage.price,GeneralPaperRetainedEndpointBitBounds.priceWidth,
    GeneralPaperScoreDPBits.profile,GeneralPaperScoreMatrixBits.matrixProfile,GeneralPaperSourceBasisControllerStorageRates.operandWidth,
    GeneralPaperSourceFinalEndpointReturnRates.affinePrice,GeneralPaperSourceInitializerReturnStorageRates.controlPrice,GeneralPaperSourceInitializerReturnStorageRates.gridPrice,
    GeneralPaperSummaryArrayExecution.arrayWord,GeneralPaperThresholdScanBits.profile,GeneralPaperBasisAffineStorage.price,
    GeneralPaperBasisStepBits.profile,GeneralPaperInitializerControlStorage.price,GeneralPaperNativeEndpointAnchorStorage.scalarCap,
    GeneralPaperNativeEndpointAnchor.width,GeneralPaperNativeEndpointColumnsStorage.fieldPrice,GeneralPaperNativePayloadFillStorage.frameProfile,
    GeneralPaperRawEndpointReturnStorage.evaluationPrice,GeneralPaperScoreDPBits.initialProfile,GeneralPaperScoreDPBits.stepProfile,
    GeneralPaperScoreMatrixBits.fieldProfile,GeneralPaperSourceFinalEndpointReturnRates.operandWidth,GeneralPaperSourceInitializerControlStorageRates.operandWidth,
    GeneralPaperSourceInitializerReturnStorageRates.packedPrice,GeneralPaperSourceInitializerReturnStorageRates.storedPrice,GeneralPaperThresholdScanBits.comparisonWidth,
    GeneralPaperBasisGridPackingPrice.profile,GeneralPaperEncodedScalarStorage.natBits,GeneralPaperEndpointPriceControl.profile,
    GeneralPaperFinalPolytopeStorage.price,GeneralPaperNativeEndpointAnchorStorage.callbackPrice,GeneralPaperNativePayloadFillStorage.metadataCap,
    GeneralPaperScoreBitPrimitive.resourceWidth,GeneralPaperScoreMatrixBits.entryProfile,GeneralPaperSourceBasisGridPackingStorageRates.operandWidth,
    GeneralPaperSourceFinalCheckStorageRates.operandWidth,GeneralPaperSourceInitializerTableStorageRates.operandWidth,GeneralPaperFinalPolytopeBits.profile,
    GeneralPaperHighSearchPriceFacts.profile,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperScoreMatrixBits.scoreProfile,
    GeneralPaperSourceRawAffineStorageRates.operandWidth,GeneralPaperBoundedQuotient.bitProfile,GeneralPaperFinalRefinementPrice.profile,
    GeneralPaperHighBlockerPrice.profile,GeneralPaperHighSearchPriceControl.profile,GeneralPaperParametricPriceProfiles.profile,
    GeneralPaperScoreArgumentBits.argumentProfile,GeneralPaperStaticScanPrice.profile,GeneralPaperBoundedQuotient.heightBudget,
    GeneralPaperFinalRefinementPrice.envelope,GeneralPaperFixedViolationPrice.profile,GeneralPaperParametricRecursionPrice.profile,
    GeneralPaperParametricStageBits.profile,GeneralPaperScoreArgumentBits.height,GeneralPaperAffineStepPrice.profile,
    GeneralPaperSourceColumnCallerStorageRates.sourceProfile,GeneralPaperSourceColumnCallerStorageRates.unitPrice,GeneralPaperRetainedSourceColumnCallerStorage.profile,
    GeneralPaperRetainedSourceColumnCallerStorage.metadataCap,GeneralPaperRetainedSourceColumnCallerStorage.price,GeneralPaperSourceUnitCallerStorageRates.quantizationPrice,
    GeneralPaperSourceUnitCallerStorageRates.normalizationPrice,GeneralPaperSourceUnitCallerStorageRates.operandCap,GeneralPaperDictionaryNormalizationStorage.price,
    GeneralPaperDivisibleColumnsParentStorage.price,GeneralPaperDictionaryNormalizationStorage.scalePrice,GeneralPaperEnclosingSourceOwners.rowsProfile,
    GeneralPaperQuantizedMatrixParentStorage.price,GeneralPaperDictionaryNormalizationStorage.fieldPrice,GeneralPaperQuantizedMatrixParentStorage.callbackPrice,
    GeneralPaperUnitSourceCallerStorage.price,GeneralPaperQuantizedMatrixParentStorage.fieldPrice,GeneralPaperRationalArrayScaleStorage.price,
    GeneralPaperColumnInputStorage.price,GeneralPaperQuantizedColumnParentStorage.price,GeneralPaperRationalArrayScaleStorage.callbackPrice,
    GeneralPaperQuantizedAnchorStorage.price,GeneralPaperQuantizedLabelScatterStorage.price,GeneralPaperRepresentativeSortStorage.price,
    GeneralPaperNativeIndexedScatterStorage.price,GeneralPaperNativeRepresentativeSort.profile,GeneralPaperQuantizedAnchorStorage.callbackPrice,
    GeneralPaperQuantizedLabelScatterStorage.callbackPrice,GeneralPaperNativeBlockLabelStorage.price,GeneralPaperPricedSort.profile,
    GeneralPaperQuantizedAnchorStorage.operandWord,GeneralPaperNativeBlockLabelStorage.magnitude,GeneralPaperNativeGrowingQuotientStorage.workCap,
    GeneralPaperSourcePreparedPairOwners.price,GeneralPaperSourceCompilerPairStorageRates.price,GeneralPaperRetainedFieldValuesStorage.price,
    GeneralPaperRetainedFieldValuesStorage.callbackPrice,GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperReducedValueArrayPrice.width,GeneralPaperFastRationalMajorant.model,GeneralPaperSourceRayStorageWidth.gridWord]
  simp only [Nat.add_mul,Nat.mul_add,Nat.add_assoc]
  change Soft bitRate _
  source_time

theorem lift_source {f : Input → ℕ} (h : Soft GeneralPaperSourceCallerSharpWork.bitRate f) : Soft bitRate f :=
  rate_mono h (fun _x => Nat.le_add_left _ _)

theorem collapse (x : Input) (cap : ℕ) (h : x.m≤cap*accuracy x) :
    bitRate x≤((cap+1)^2+cap+2)*monomial 3 0 6 x := by
  have hf := GeneralPaperSourceCallerSharpWork.reduced_field_bound x cap h
  have h0 := GeneralPaperSourceCallerSharpWork.field_shift x (cap+1) 4 4 hf
  have h1 := GeneralPaperSourceCallerSharpWork.field_shift x (cap+1) 3 5 hf
  have h2 := GeneralPaperSourceCallerSharpWork.bit_collapse x cap h
  have hTop := h0.trans (Nat.mul_le_mul_left (cap+1) h1)
  unfold bitRate
  calc
    monomial 5 0 4 x+GeneralPaperSourceCallerSharpWork.bitRate x≤
        (cap+1)*((cap+1)*monomial 3 0 6 x)+(cap+2)*monomial 3 0 6 x := Nat.add_le_add hTop h2
    _=((cap+1)^2+cap+2)*monomial 3 0 6 x := by ring

end Blotto.GeneralPaperCompilerSharpWork
