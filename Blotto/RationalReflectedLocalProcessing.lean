import Blotto.RationalNestedProcessingLedger
import Blotto.CachedControlOutputMap

/-! Reflected local processing preserves the full data/callback and Boolean
ledger through the actual output map. The reflection map's own rational work,
fallback, parent construction and physical backend remain separate. -/

namespace Blotto.RationalFourInput

noncomputable def reflectedLocalProcessingWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let system := i.reflectedResourceSystem hcase
  rationalInitialDataBitCost model system.capacity system.initial +
    (i.reflectedMachine hcase K outerBits scalarBits).cachedCallbackWork
      (system.localDataOutputCharge model primitive copyResources K outerBits scalarBits)
      N bits (.state system.samplingStart) pos hpos +
    (i.reflectedMachine hcase K outerBits scalarBits).cachedControlWork (fun _ => true) (fun w => 4 * w)
      FixedWordCoin.bodyAllowance N bits (.state system.samplingStart) pos hpos

theorem reflectedLocalProcessingWork_refines (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedLocalProcessingWork hcase model primitive copyResources K outerBits scalarBits N bits pos hpos =
      (i.reflectedResourceSystem hcase).localProcessingWork model primitive copyResources K outerBits scalarBits N bits pos hpos := by
  unfold RationalNestedResourceSystem.localProcessingWork RationalNestedResourceSystem.localBooleanControlWork
  rw [RationalNestedResourceSystem.localDataOutputBitWork_singlePath]
  unfold reflectedLocalProcessingWork reflectedMachine
  dsimp only
  rw [WordStateMachine.cachedCallbackWork_mapped, WordStateMachine.cachedControlWork_mapped]

theorem FieldsHeight.reflectedLocalProcessingWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedLocalProcessingWork hcase model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      58 * RationalNestedInput.preparationNumericBitWork c K +
        498000 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 73) +
          76 * ((expressionHeightBudget (max s (K + 2)) 68 + 1) * 19) +
            (24 * ((expressionHeightBudget (max s (K + 2)) 68 + 1) * 19) + 28) * (40 + 2 * (N - pos)) := by
  let w := max s (K + 2)
  have hw := hs.trans (le_max_left s (K + 2))
  have hSystem := (h.mono (le_max_left s (K + 2))).reflectedResourceSystem hw hcase
  have hp := hSystem.localProcessingWork_bound (hw.trans (expressionHeightBudget_ge_input w 14))
    model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos
  rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 14))] at hp
  unfold RationalNestedResourceSystem.localDataOutputWidth RationalNestedResourceSystem.localControlWordHeight at hp
  simp only [expressionHeightBudget_comp] at hp
  exact (i.reflectedLocalProcessingWork_refines hcase model primitive copyResources K
    outerBits scalarBits N bits pos hpos).le.trans hp

end Blotto.RationalFourInput
