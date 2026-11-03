import Blotto.RationalPRGSharedCouplingLedger

/-! Source, one-time packing, reached terminal coupling/emission and direct
fallback are priced on one paper packet. The logical-resource-store and
conservative full-array-copy interpretations are stated separately. Input
decoding, metadata, allocation ownership and concrete backend costs are open. -/

namespace Blotto.RationalPRGInput

noncomputable def richSharedProcessingWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richSharedSourceAndPackingWork model copyResources K bits +
    i.richNativeSystem.sharedPaperCouplingWork model primitive copyResources K bits +
      i.richNativeSystem.paperFallbackWork K bits

noncomputable def poorSharedProcessingWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorSharedSourceAndPackingWork model copyResources K bits +
    i.poorNativeSystem.sharedPaperCouplingWork model primitive copyResources K bits +
      i.poorNativeSystem.paperFallbackWork K bits

theorem richSharedProcessingWork_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSharedProcessingWork model primitive copyResources K bits ≤
      (32 * n + 15) * model.rat i.sourceAndPackingWidth + i.paperCouplingBound model c K +
        2 * n * model.rat (1 + 2 * (3 + i.inputWordWidth)) :=
  Nat.add_le_add (Nat.add_le_add (i.richSharedSourceAndPackingWork_bound model copyResources K bits)
    (i.sharedPaperCouplingWork_bounds model primitive c hPrimitive copyResources K bits).1)
      (i.paperFallbackWork_bounds model K bits).1

theorem poorSharedProcessingWork_logical_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedProcessingWork model primitive false K bits ≤
      (192 * n + 15) * model.rat i.sourceAndPackingWidth +
        (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6002) + i.paperCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.inputWordWidth)) :=
  Nat.add_le_add (Nat.add_le_add (i.poorSharedSourceAndPackingWork_logical_bound model K bits)
    (i.sharedPaperCouplingWork_bounds model primitive c hPrimitive false K bits).2)
      (i.paperFallbackWork_bounds model K bits).2

theorem poorSharedProcessingWork_fullCopy_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedProcessingWork model primitive true K bits ≤
      (2 * n * n + 188 * n + 15) * model.rat i.sourceAndPackingWidth +
        (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6002) + i.paperCouplingBound model c K +
          2 * n * model.rat (1 + 2 * (3 + i.inputWordWidth)) :=
  Nat.add_le_add (Nat.add_le_add (i.poorSharedSourceAndPackingWork_fullCopy_bound model K bits)
    (i.sharedPaperCouplingWork_bounds model primitive c hPrimitive true K bits).2)
      (i.paperFallbackWork_bounds model K bits).2

end Blotto.RationalPRGInput
