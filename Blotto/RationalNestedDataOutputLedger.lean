import Blotto.RationalNestedOutputWork
import Blotto.RationalNestedPacketCopyWork

/-! Source/store/retention/categorical, repeated factories, start words,
packet copies and one-time decoded output add on one indexed callback path.
This data/primitive ledger excludes Boolean control, later maps/fallback and
address/metadata/backend/allocator/ownership costs. -/

namespace Blotto.RationalNestedResourceSystem

def localDataOutputWidth (s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget s 59

theorem localDataOutputWidth_components (s : ℕ) :
    32 * expressionHeightBudget s 7 + 31 ≤ localDataOutputWidth s ∧
      categoricalRequestWidth 18 (expressionHeightBudget s 54) ≤ localDataOutputWidth s ∧
        terminalFactoryWidth s ≤ localDataOutputWidth s ∧
          1 + 2 * expressionHeightBudget s 7 ≤ localDataOutputWidth s ∧
            terminalOutputWidth s ≤ localDataOutputWidth s := by
  have h12 : expressionHeightBudget s 12 = 32 * expressionHeightBudget s 7 + 31 := by
    rw [show 12 = 7 + 5 by decide, ← expressionHeightBudget_comp]
    change (expressionHeightBudget s 7 + 1) * 32 - 1 = _
    omega
  have h59 : expressionHeightBudget s 59 = 32 * expressionHeightBudget s 54 + 31 := by
    rw [show 59 = 54 + 5 by decide, ← expressionHeightBudget_comp]
    change (expressionHeightBudget s 54 + 1) * 32 - 1 = _
    omega
  have h12le := expressionHeightBudget_mono s (by decide : 12 ≤ 59)
  have h54le := expressionHeightBudget_mono s (by decide : 54 ≤ 59)
  have h7le := expressionHeightBudget_mono s (by decide : 7 ≤ 59)
  have h57le := expressionHeightBudget_mono s (by decide : 57 ≤ 59)
  unfold localDataOutputWidth terminalFactoryWidth terminalOutputWidth categoricalRequestWidth
  omega

noncomputable def localDataOutputBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.localDataCallbackFactoryAndStartBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.terminalPacketCopyBitWork K outerBits scalarBits N bits pos hpos +
      i.terminalDecodedEmissionBitWork model primitive K outerBits scalarBits N bits pos hpos

noncomputable def localDataOutputCharge (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : i.SamplingState → ℕ := fun cursor =>
  i.localCallbackBitCharge model copyResources K outerBits cursor +
    WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
      (i.terminalProfileFactoryPrice model primitive K outerBits) cursor +
    WordStateMachine.serialPreparationCharge i.phase (i.terminalStartDataPrice K outerBits) cursor +
    WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits) i.terminalPacketCopyPrice cursor +
    WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
      (i.terminalDecodedEmissionCharge model primitive K outerBits scalarBits) cursor

theorem localDataOutputBitWork_singlePath (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localDataOutputBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos =
      rationalInitialDataBitCost model i.capacity i.initial +
        (i.machine K outerBits scalarBits).cachedCallbackWork (i.localDataOutputCharge model primitive copyResources K outerBits scalarBits)
          N bits (.state i.samplingStart) pos hpos := by
  unfold localDataOutputBitWork terminalPacketCopyBitWork terminalDecodedEmissionBitWork localDataOutputCharge
  rw [localDataCallbackFactoryAndStartBitWork_singlePath]
  simp only [WordStateMachine.cachedCallbackWork_add, Nat.add_assoc]

theorem FieldsHeight.localDataOutputBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localDataOutputBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      58 * RationalNestedInput.preparationNumericBitWork c K + 498000 * model.rat (localDataOutputWidth s) := by
  let price := model.rat (localDataOutputWidth s)
  have widths := localDataOutputWidth_components s
  have hSource := model.monotone widths.1
  have hCat := model.monotone widths.2.1
  have hFactory := model.monotone widths.2.2.1
  have hPacket := model.monotone widths.2.2.2.1
  have hOutput := model.monotone widths.2.2.2.2
  have hd := h.localDataCallbackFactoryAndStartBitWork_bound hs model primitive c hPrimitive copyResources K hPrecision
    outerBits scalarBits N bits pos hpos
  have hp := h.terminalPacketCopyBitWork_bound hs model K outerBits scalarBits N bits pos hpos
  have ho := h.terminalDecodedEmissionBitWork_bound hs model primitive c hPrimitive K hPrecision outerBits scalarBits N bits pos hpos
  have hCopy : (if copyResources then 407 else 399) ≤ 407 := by cases copyResources <;> decide
  change model.rat (32 * expressionHeightBudget s 7 + 31) ≤ price at hSource
  change model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) ≤ price at hCat
  change model.rat (terminalFactoryWidth s) ≤ price at hFactory
  change model.rat (1 + 2 * expressionHeightBudget s 7) ≤ price at hPacket
  change model.rat (terminalOutputWidth s) ≤ price at hOutput
  unfold localDataOutputBitWork
  nlinarith

end Blotto.RationalNestedResourceSystem
