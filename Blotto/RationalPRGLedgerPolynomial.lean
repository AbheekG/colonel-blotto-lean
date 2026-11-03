import Blotto.RationalPRGRouteBackendFrameBound
import Blotto.NaturalPolynomialEnvelope

/-! Polynomial growth of the existing complete labelled request envelope in
the schoolbook rational majorant. This does not assert a native primitive
implementation or close the still separate execution/space refinement. -/

namespace Blotto.RationalPRGBinaryRequest

def completeLedgerFrameBound (model : RationalCostModel) (c : ℕ) (copyResources : Bool)
    (length seedLength : ℕ) : ℕ :=
  executionFrameBound model c copyResources length seedLength + gameMetadataBound c length +
    decoderMetadataBound c length + outputMetadataFrameBound c length +
      9072 * dyadicMidpointMetadataBound c (length + 6) + positionReaderFrameBound c length +
        scalarReaderFrameBound c length + constructionMetadataFrameBound c length +
          entryConstructionMetadataFrameBound c length + packetRoutingMetadataFrameBound c length +
            packingCopyFrameBound c length + groupTableConstructionFrameBound c length +
              routeBackendFrameBound model c length

theorem executionWithRouteBackendWork_complete_bound (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithRouteBackendWork model primitive c copyResources rich frame seed ≤
      completeLedgerFrameBound model c copyResources frame.length seed.length :=
  executionWithRouteBackendWork_frame_bound model primitive c hPrimitive copyResources rich frame seed

def ledgerInputSize (x : ℕ × ℕ × ℕ) : ℕ := x.1 + x.2.1 + x.2.2

theorem ledgerInputSize_first : NaturalPolynomialEnvelope ledgerInputSize (fun x => x.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold ledgerInputSize; omega)

theorem ledgerInputSize_second : NaturalPolynomialEnvelope ledgerInputSize (fun x => x.2.1) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold ledgerInputSize; omega)

theorem ledgerInputSize_third : NaturalPolynomialEnvelope ledgerInputSize (fun x => x.2.2) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold ledgerInputSize; omega)

open Lean Meta Elab Tactic in
elab "polynomial_envelope" : tactic => do
  for _ in [:10000] do
    if (← getGoals).isEmpty then return
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let fn := target.getAppArgs.back!
    if fn.getAppFn.constName? == some ``Prod.fst then
      evalTactic (← `(tactic| exact ledgerInputSize_first))
      continue
    let .lam _ _ body _ := fn | throwError "expected envelope lambda: {target}"
    let body := body.headBeta
    let rule ← match body.getAppFn.constName? with
      | some ``HAdd.hAdd => `(tactic| apply NaturalPolynomialEnvelope.add)
      | some ``HMul.hMul => `(tactic| apply NaturalPolynomialEnvelope.mul)
      | some ``HPow.hPow => `(tactic| apply NaturalPolynomialEnvelope.pow)
      | some ``HSub.hSub => `(tactic| apply NaturalPolynomialEnvelope.sub)
      | some ``Max.max => `(tactic| apply NaturalPolynomialEnvelope.max)
      | some ``binaryWordWidth => `(tactic| apply NaturalPolynomialEnvelope.wordWidth)
      | some ``expressionHeightBudget => `(tactic| apply NaturalPolynomialEnvelope.height)
      | _ =>
        if body.hasLooseBVars then
          `(tactic| first | exact ledgerInputSize_first | exact ledgerInputSize_second | exact ledgerInputSize_third)
        else `(tactic| exact NaturalPolynomialEnvelope.constant _ _)
    evalTactic rule
  throwError "polynomial envelope expression exceeds structural step budget"


theorem readPrecisionBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => readPrecisionBound RationalCostModel.schoolbook x.1 x.2.1) := by
  simp only [Blotto.BinaryRatListFrame.decodingFramePrice,
    Blotto.RationalPRGBinaryInput.decodingBound,
    Blotto.RationalPRGBinaryInput.parsedRecognitionBound,
    Blotto.RationalPRGBinaryRequest.readPrecisionBound,
    Blotto.RationalPRGCheckCode.recognitionWidth,
    Blotto.RationalCostModel.schoolbook]
  polynomial_envelope

theorem seedPreparationBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => seedPreparationBound x.1 x.2.1 x.2.2) := by
  simp only [Blotto.RationalPRGBinaryRequest.seedPreparationBound]
  polynomial_envelope

theorem samplingFrameBound_no_copy_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => samplingFrameBound RationalCostModel.schoolbook x.1 false x.2.1) := by
  simp only [Blotto.RationalLottoResourceSystem.coinBitBudget,
    Blotto.RationalNestedInput.preparationNumericBitWork,
    Blotto.RationalPRGBinaryRequest.samplingFrameBound,
    Blotto.RationalPRGOriginalInput.dispatchEnvelope,
    Blotto.RationalPRGOriginalInput.processingSourceCoefficient,
    Blotto.RationalTerminalLotto.terminalCouplingWordHeight,
    Blotto.RationalCostModel.schoolbook, Bool.false_eq_true, ite_false]
  polynomial_envelope

theorem samplingFrameBound_copy_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => samplingFrameBound RationalCostModel.schoolbook x.1 true x.2.1) := by
  simp only [Blotto.RationalLottoResourceSystem.coinBitBudget,
    Blotto.RationalNestedInput.preparationNumericBitWork,
    Blotto.RationalPRGBinaryRequest.samplingFrameBound,
    Blotto.RationalPRGOriginalInput.dispatchEnvelope,
    Blotto.RationalPRGOriginalInput.processingSourceCoefficient,
    Blotto.RationalTerminalLotto.terminalCouplingWordHeight,
    Blotto.RationalCostModel.schoolbook, ite_true]
  polynomial_envelope

theorem gameMetadataBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => gameMetadataBound x.1 x.2.1) := by
  simp only [Blotto.BinaryNatFrame.lengthMetadataBound,
    Blotto.RationalPRGBinaryInput.checkedTableBound,
    Blotto.RationalPRGBinaryInput.rawMetadataBound,
    Blotto.RationalPRGBinaryRequest.gameMetadataBound]
  polynomial_envelope

theorem decoderMetadataBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => decoderMetadataBound x.1 x.2.1) := by
  simp only [Blotto.BinaryNatFrame.lengthMetadataBound,
    Blotto.BinaryNatFrame.payloadMetadataBound,
    Blotto.BinaryPayload.decoderMetadataBound,
    Blotto.RationalPRGBinaryInput.rawDecoderMetadataBound,
    Blotto.RationalPRGBinaryRequest.decoderMetadataBound]
  polynomial_envelope

theorem outputMetadataFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => outputMetadataFrameBound x.1 x.2.1) := by
  simp only [Blotto.BinaryNatFrame.encodingMetadataBound,
    Blotto.BinaryRatListFrame.rowEncodingMetadataBound,
    Blotto.RationalPRGBinaryRequest.outputMetadataFrameBound,
    Blotto.RationalPRGOriginalInput.outputMetadataBound,
    Blotto.indexedLoopMetadataBound]
  polynomial_envelope

theorem dyadicMidpointMetadataBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => dyadicMidpointMetadataBound x.1 (x.2.1 + 6)) := by
  simp only [Blotto.dyadicMidpointMetadataBound,
    Blotto.indexedLoopMetadataBound]
  polynomial_envelope

theorem positionReaderFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => positionReaderFrameBound x.1 x.2.1) := by
  simp only [Blotto.RationalPRGBinaryRequest.positionReaderFrameBound,
    Blotto.positionReaderUnitBound]
  polynomial_envelope

theorem scalarReaderFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => scalarReaderFrameBound x.1 x.2.1) := by
  simp only [Blotto.RationalPRGBinaryRequest.scalarReaderFrameBound,
    Blotto.RationalPRGInput.scalarReaderUnitBound]
  polynomial_envelope

theorem constructionMetadataFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => constructionMetadataFrameBound x.1 x.2.1) := by
  simp only [Blotto.PreparedSegmentDescriptor.preparationMetadataBound,
    Blotto.RationalExpression.metadataInstructionBound,
    Blotto.RationalNestedInput.familyInputMetadataBound,
    Blotto.RationalNestedInput.firstConditionalMetadataBound,
    Blotto.RationalNestedInput.firstMidpointConstructionMetadataBound,
    Blotto.RationalNestedInput.paddedResidualMetadataBound,
    Blotto.RationalNestedInput.profileConstructionMetadataBound,
    Blotto.RationalNestedInput.secondProfileMetadataBound,
    Blotto.RationalNestedInput.secondUniformMetadataBound,
    Blotto.RationalNestedInput.thirdProfileMetadataBound,
    Blotto.RationalNestedResidualCode.compilerMetadataBound,
    Blotto.RationalNestedSpec.profileConstructionMetadataBound,
    Blotto.RationalNestedSpec.sortingFieldsMetadataBound,
    Blotto.RationalPRGBinaryRequest.constructionMetadataFrameBound,
    Blotto.RationalPermutationCode.descriptorMetadataBound,
    Blotto.RationalTerminalResources.inputConstructionMetadataBound,
    Blotto.RationalTerminalResources.profileConstructionMetadataBound,
    Blotto.RationalThreeInputCode.constructionMetadataBound,
    Blotto.RationalThreeSpecCode.constructionMetadataBound,
    Blotto.RationalThreeSpecCode.endpointConstructionMetadataBound,
    Blotto.indexedLoopMetadataBound,
    Blotto.rationalEnvironmentMetadataBound]
  polynomial_envelope

theorem entryConstructionMetadataFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => entryConstructionMetadataFrameBound x.1 x.2.1) := by
  simp only [Blotto.RationalFourSpec.wrapperConstructionMetadataBound, Blotto.PreparedSegmentDescriptor.preparationMetadataBound,
    Blotto.RationalExpression.metadataInstructionBound,
    Blotto.RationalFourInput.entryConstructionMetadataBound,
    Blotto.RationalFourInput.entryParameterMetadataBound,
    Blotto.RationalFourInput.gluingConstructionMetadataBound,
    Blotto.RationalFourInput.smallParentConstructionMetadataBound,
    Blotto.RationalFourParameterTable.preparationMetadataBound,
    Blotto.RationalMergeFourInput.constructionMetadataBound,
    Blotto.RationalMixedGroupSpec.entryConstructionMetadataBound,
    Blotto.RationalOverlapFormula.slotIndexMetadataUnitBound,
    Blotto.RationalPRGBinaryRequest.entryConstructionMetadataFrameBound,
    Blotto.RationalSplitCode.descriptorMetadataBound,
    Blotto.RationalTerminalLotto.entryConstructionMetadataBound,
    Blotto.RationalThreeInputCode.constructionMetadataBound,
    Blotto.RationalThreeSpecCode.constructionMetadataBound,
    Blotto.RationalUniformGroupSpec.entryConstructionMetadataBound,
    Blotto.indexedLoopMetadataBound,
    Blotto.rationalEnvironmentMetadataBound]
  polynomial_envelope

theorem packetRoutingMetadataFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => packetRoutingMetadataFrameBound x.1 x.2.1) := by
  simp only [Blotto.RationalExpression.metadataInstructionBound,
    Blotto.RationalPRGBinaryRequest.packetRoutingMetadataFrameBound,
    Blotto.RationalTerminalLotto.groupPacketMetadataBound,
    Blotto.RationalTerminalLotto.packetRoutingMetadataBound,
    Blotto.RationalTerminalPacking.entryMetadataBound,
    Blotto.RationalTerminalPacking.routingMetadataBound,
    Blotto.indexedLoopMetadataBound,
    Blotto.rationalEnvironmentMetadataBound]
  polynomial_envelope

theorem packingCopyFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => packingCopyFrameBound x.1 x.2.1) := by
  simp only [Blotto.RationalPRGBinaryRequest.packingCopyFrameBound,
    Blotto.RationalPackingMetadata.bodyBound,
    Blotto.RationalPackingMetadata.groupCellBound,
    Blotto.RationalPackingMetadata.labelBound,
    Blotto.RationalPackingMetadata.packedBound,
    Blotto.RationalTerminalLotto.packingCopyBound,
    Blotto.RationalTerminalPacking.routeArrayCopyBound,
    Blotto.RationalTerminalPacking.routePayloadWidth,
    Blotto.indexedLoopMetadataBound]
  polynomial_envelope

theorem groupTableConstructionFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => groupTableConstructionFrameBound x.1 x.2.1) := by
  simp only [Blotto.RationalPRGBinaryRequest.groupTableConstructionFrameBound,
    Blotto.RationalTerminalLotto.groupEntryPayloadWidth,
    Blotto.RationalTerminalLotto.groupTableConstructionBound,
    Blotto.indexedLoopMetadataBound]
  polynomial_envelope

theorem routeBackendFrameBound_polynomial : NaturalPolynomialEnvelope ledgerInputSize
    (fun x => routeBackendFrameBound RationalCostModel.schoolbook x.1 x.2.1) := by
  simp only [Blotto.BinaryAddressFormation.encodedWorkBound,
    Blotto.BinaryAddressFormation.operandBound,
    Blotto.BinaryAddressFormation.workBound,
    Blotto.BinaryNatFrame.encodingMetadataBound,
    Blotto.BinaryNatFrame.lengthMetadataBound,
    Blotto.BinaryNatFrame.payloadMetadataBound,
    Blotto.BinaryPayload.decoderMetadataBound,
    Blotto.BinaryRouteFrame.decodingBound,
    Blotto.BinaryRouteFrame.encodingBound,
    Blotto.BinaryRouteFrame.naturalMetadataBound,
    Blotto.BinaryRouteSlot.preparationBound,
    Blotto.BinaryRouteSlot.readingBound,
    Blotto.FixedWordRegion.accessBound,
    Blotto.FixedWordRegion.addressWidth,
    Blotto.FixedWordRegion.formedAccessBound,
    Blotto.RationalLottoResourceSystem.bitRouteSlotWidth,
    Blotto.RationalPRGBinaryRequest.routeBackendFrameBound,
    Blotto.RationalTerminalLotto.routeReadFormationBound,
    Blotto.RationalTerminalLotto.terminalRouteBackendBound,
    Blotto.RationalTerminalPacking.routeBitBuildBound,
    Blotto.RationalTerminalPacking.routePayloadWidth,
    Blotto.indexedLoopMetadataBound,
    Blotto.RationalCostModel.schoolbook]
  polynomial_envelope

theorem samplingFrameBound_polynomial (copyResources : Bool) :
    NaturalPolynomialEnvelope ledgerInputSize
      (fun x => samplingFrameBound RationalCostModel.schoolbook x.1 copyResources x.2.1) := by
  cases copyResources
  · exact samplingFrameBound_no_copy_polynomial
  · exact samplingFrameBound_copy_polynomial

theorem completeLedgerFrameBound_polynomial (copyResources : Bool) :
    NaturalPolynomialEnvelope ledgerInputSize
      (fun x => completeLedgerFrameBound RationalCostModel.schoolbook x.1 copyResources x.2.1 x.2.2) := by
  exact (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add (NaturalPolynomialEnvelope.add readPrecisionBound_polynomial
    seedPreparationBound_polynomial)
    (samplingFrameBound_polynomial copyResources))
    gameMetadataBound_polynomial)
    decoderMetadataBound_polynomial)
    outputMetadataFrameBound_polynomial)
    (NaturalPolynomialEnvelope.mul (NaturalPolynomialEnvelope.constant ledgerInputSize 9072) dyadicMidpointMetadataBound_polynomial))
    positionReaderFrameBound_polynomial)
    scalarReaderFrameBound_polynomial)
    constructionMetadataFrameBound_polynomial)
    entryConstructionMetadataFrameBound_polynomial)
    packetRoutingMetadataFrameBound_polynomial)
    packingCopyFrameBound_polynomial)
    groupTableConstructionFrameBound_polynomial)
    routeBackendFrameBound_polynomial)

theorem executionWithRouteBackendWork_polynomial :
    ∃ C d : ℕ, ∀ (primitive : ℕ → ℕ) (c : ℕ),
      (∀ w, primitive w ≤ c * w) → ∀ (copyResources rich : Bool) (frame seed : List Bool),
      executionWithRouteBackendWork RationalCostModel.schoolbook primitive c copyResources rich frame seed ≤
        C * (c + frame.length + seed.length + 1) ^ d := by
  have hBoth := NaturalPolynomialEnvelope.add
    (completeLedgerFrameBound_polynomial false) (completeLedgerFrameBound_polynomial true)
  rcases hBoth with ⟨C, d, hBoth⟩
  refine ⟨C, d, ?_⟩
  intro primitive c hPrimitive copyResources rich frame seed
  have hCost := executionWithRouteBackendWork_complete_bound RationalCostModel.schoolbook
    primitive c hPrimitive copyResources rich frame seed
  have hSum := hBoth (c, frame.length, seed.length)
  have hSelect : completeLedgerFrameBound RationalCostModel.schoolbook c copyResources frame.length seed.length ≤
      completeLedgerFrameBound RationalCostModel.schoolbook c false frame.length seed.length +
        completeLedgerFrameBound RationalCostModel.schoolbook c true frame.length seed.length := by
    cases copyResources <;> omega
  simpa only [ledgerInputSize, Nat.add_assoc] using hCost.trans (hSelect.trans hSum)

end Blotto.RationalPRGBinaryRequest
