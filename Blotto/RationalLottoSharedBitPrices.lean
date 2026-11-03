import Blotto.RationalLottoSharedWork
import Blotto.RationalLottoWordExtractionPrice
import Blotto.RationalLottoClassificationPrice

/-! Pair arithmetic/word extraction, selected stores and retention prices
are transferred by event-work equality to the primary one-state source prefix.
Boolean control, physical ownership and terminal costs remain separate. -/

namespace Blotto.RationalLottoResourceSystem

def sharedSourcePairBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (R : ℕ) (bits : Fin R → Bool) : ℕ := i.sharedSourceCallbackWork (rationalResourcePairCharge model) R bits

theorem sharedSourcePairBitCost_refines {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedSourcePairBitCost model R bits = i.cachedSourcePairBitCost model K R outerBits scalarBits bits :=
  i.sharedSourceCallbackWork_refines (rationalResourcePairCharge model) K R outerBits scalarBits bits

theorem sharedSourcePairBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sharedSourcePairBitCost model R choiceBits ≤
      96 * n * model.rat (3 + 2 * binaryWordWidth D) := by
  rw [i.sharedSourcePairBitCost_refines model K R outerBits scalarBits choiceBits]
  exact i.cachedSourcePairBitCost_bound model D hD hB hL hR K R outerBits scalarBits choiceBits

def sharedSourceRequestBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (R : ℕ) (bits : Fin R → Bool) : ℕ := i.sharedSourceCallbackWork (rationalResourcePairRequestCharge model) R bits

theorem sharedSourceRequestBitCost_refines {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedSourceRequestBitCost model R bits = i.cachedSourceRequestBitCost model K R outerBits scalarBits bits :=
  i.sharedSourceCallbackWork_refines (rationalResourcePairRequestCharge model) K R outerBits scalarBits bits

theorem sharedSourceRequestBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sharedSourceRequestBitCost model R choiceBits ≤
      98 * n * model.rat (3 + 2 * binaryWordWidth D) := by
  rw [i.sharedSourceRequestBitCost_refines model K R outerBits scalarBits choiceBits]
  exact i.cachedSourceRequestBitCost_bound model D hD hB hL hR K R outerBits scalarBits choiceBits

def sharedSourceStoreBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel) (copyResources : Bool)
    (R : ℕ) (bits : Fin R → Bool) : ℕ := i.sharedSourceCallbackWork (rationalResourceStoreBitCharge model copyResources) R bits

theorem sharedSourceStoreBitCost_refines {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel) (copyResources : Bool)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedSourceStoreBitCost model copyResources R bits = i.cachedSourceStoreBitCost model copyResources K R outerBits scalarBits bits :=
  i.sharedSourceCallbackWork_refines (rationalResourceStoreBitCharge model copyResources) K R outerBits scalarBits bits

theorem sharedSourceStoreBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (copyResources : Bool) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sharedSourceStoreBitCost model copyResources R choiceBits ≤
      (if copyResources then 2 * n + 30 else 32) * (n - 1) * model.rat (8 * binaryWordWidth D + 23) := by
  rw [i.sharedSourceStoreBitCost_refines model copyResources K R outerBits scalarBits choiceBits]
  exact i.cachedSourceStoreBitCost_bound model copyResources D hD hB hL hR K R outerBits scalarBits choiceBits

def sharedSourceRetainedBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (R : ℕ) (bits : Fin R → Bool) : ℕ := i.sharedSourceCallbackWork (rationalResourceRetainedBitCharge model) R bits

theorem sharedSourceRetainedBitCost_refines {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedSourceRetainedBitCost model R bits = i.cachedSourceRetainedBitCost model K R outerBits scalarBits bits :=
  i.sharedSourceCallbackWork_refines (rationalResourceRetainedBitCharge model) K R outerBits scalarBits bits

theorem sharedSourceRetainedBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sharedSourceRetainedBitCost model R choiceBits ≤
      10 * (n - 1) * model.rat (3 + 2 * binaryWordWidth D) := by
  rw [i.sharedSourceRetainedBitCost_refines model K R outerBits scalarBits choiceBits]
  exact i.cachedSourceRetainedBitCost_bound model D hD hB hL hR K R outerBits scalarBits choiceBits

end Blotto.RationalLottoResourceSystem
