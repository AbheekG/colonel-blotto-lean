import Blotto.RationalNestedSourceLedger
import Blotto.CachedCallbackAdditivity
import Blotto.RationalFourSmallHeight

/-! Source and terminal components equal one callback-price observer on the
same local path. Reflection maps output values without changing this work.
The four-variable specialization keeps explicit remaining cost obligations. -/

namespace Blotto.RationalNestedResourceSystem

def localCallbackBitCharge (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (outerBits : Fin K → Bool) : i.SamplingState → ℕ := fun cursor =>
  WordStateMachine.serialSourceCharge (fun q : i.PhaseCursor => rationalResourcePairRequestCharge model q.1) cursor +
    WordStateMachine.serialSourceCharge (fun q : i.PhaseCursor => rationalResourceStoreBitCharge model copyResources q.1) cursor +
    WordStateMachine.serialSourceCharge (fun q : i.PhaseCursor => rationalResourceRetainedBitCharge model q.1) cursor +
    WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
      (fun _ => categoricalCallbackBitCost model) cursor

theorem localSourceAndTerminalBitWork_singlePath (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localSourceAndTerminalBitWork model copyResources K outerBits scalarBits N bits pos hpos =
      rationalInitialDataBitCost model i.capacity i.initial +
        (i.machine K outerBits scalarBits).cachedCallbackWork (i.localCallbackBitCharge model copyResources K outerBits)
          N bits (.state i.samplingStart) pos hpos := by
  unfold localSourceAndTerminalBitWork localSourceDataBitWork phaseRequestBitWork phaseStoreBitWork phaseRetainedBitWork terminalCategoricalBitWork localCallbackBitCharge
  simp only [WordStateMachine.cachedCallbackWork_add, Nat.add_assoc]

end Blotto.RationalNestedResourceSystem
namespace Blotto.RationalFourInput

def reflectedLocalBitWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let system := i.reflectedResourceSystem hcase
  rationalInitialDataBitCost model system.capacity system.initial +
    (i.reflectedMachine hcase K outerBits scalarBits).cachedCallbackWork
      (system.localCallbackBitCharge model copyResources K outerBits) N bits (.state system.samplingStart) pos hpos

theorem reflectedLocalBitWork_refines (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedLocalBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos =
      (i.reflectedResourceSystem hcase).localSourceAndTerminalBitWork model copyResources K outerBits scalarBits N bits pos hpos := by
  rw [RationalNestedResourceSystem.localSourceAndTerminalBitWork_singlePath]
  unfold reflectedLocalBitWork reflectedMachine
  dsimp only
  rw [WordStateMachine.cachedCallbackWork_mapped]

theorem FieldsHeight.reflectedLocalBitWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (copyResources : Bool)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedLocalBitWork hcase model copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 407 else 399) * model.rat (32 * expressionHeightBudget (max s (K + 2)) 21 + 31) +
        2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget (max s (K + 2)) 68)) := by
  let w := max s (K + 2)
  have hw : 2 ≤ w := hs.trans (le_max_left s (K + 2))
  have hSystem := (h.mono (le_max_left s (K + 2))).reflectedResourceSystem hw hcase
  have hs14 := hw.trans (expressionHeightBudget_ge_input w 14)
  have hPrecision : K + 2 ≤ expressionHeightBudget w 14 :=
    (le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 14)
  have hp := hSystem.localSourceAndTerminalBitWork_bound hs14 model copyResources K hPrecision
    outerBits scalarBits N bits pos hpos
  rw [← i.reflectedLocalBitWork_refines hcase model copyResources K outerBits scalarBits N bits pos hpos,
    expressionHeightBudget_comp, expressionHeightBudget_comp] at hp
  exact hp

end Blotto.RationalFourInput
