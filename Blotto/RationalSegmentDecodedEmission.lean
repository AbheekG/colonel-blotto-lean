import Blotto.DyadicMidpointDecodeWork
import Blotto.RationalSegmentInterpolationWork
import Blotto.RationalCategoricalCallbackWork
import Blotto.CachedCallbackAdditivity

/-! One selected segment slot pays midpoint decoding and all coordinate
interpolations. The callback ledger adds these costs to the actual categorical
primitives on the same cap/position. Descriptor/list construction, Boolean
control, counters/addresses/backend/ownership and fallback remain separate. -/

namespace Blotto.RationalSegmentLottery

def decodedInterpolationBitCost {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (K : ℕ) (scalarBits : Fin K → Bool) (slot : Fin k) : ℕ :=
  dyadicMidpointDecodeBitWork model primitive K scalarBits + l.interpolationBitCost model K scalarBits slot

theorem HeightAt.decodedInterpolationBitCost_bound {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (scalarBits : Fin K → Bool) (slot : Fin k) :
    l.decodedInterpolationBitCost model primitive K scalarBits slot ≤
      3 * K + (4 + 2 * c) * K * binaryWordWidth K + c * (K + 2) +
        11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
          13 * n * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 3) := by
  have hd := dyadicMidpointDecodeBitWork_bound model primitive c hPrimitive K scalarBits
  have hi := h.interpolationBitCost_bound hs model K scalarBits slot
  unfold decodedInterpolationBitCost
  omega

def decodedInterpolationWork {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (fallback : Fin k) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (categoricalMachine fallback).cachedEmissionWork (l.decodedInterpolationBitCost model primitive K scalarBits)
    N bits (.state l.start) pos hpos

theorem HeightAt.decodedInterpolationWork_bound {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (fallback : Fin k)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    l.decodedInterpolationWork model primitive fallback K scalarBits N bits pos hpos ≤
      3 * K + (4 + 2 * c) * K * binaryWordWidth K + c * (K + 2) +
        11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
          13 * n * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 3) := by
  apply (categoricalMachine fallback).cachedEmissionWork_bound_under (fun _ => True) _ _ _ N bits l.start trivial pos hpos
  intro state _
  cases ht : (categoricalMachine fallback).step state with
  | done slot => exact h.decodedInterpolationBitCost_bound hs model primitive c hPrimitive K scalarBits slot
  | ask a b hb hab upper lower => exact ⟨trivial, trivial⟩

theorem decodedInterpolationWork_of_none {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (fallback : Fin k) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : ((categoricalMachine fallback).runCachedIndexed N bits (.state l.start) pos hpos).1 = none) :
    l.decodedInterpolationWork model primitive fallback K scalarBits N bits pos hpos = 0 :=
  (categoricalMachine fallback).cachedEmissionWork_of_none _ N bits (.state l.start) pos hpos hNone

def dataAndCallbackBitWork {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (fallback : Fin k) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  l.choiceCallbackBitWork model fallback K scalarBits N bits pos hpos +
    l.decodedInterpolationWork model primitive fallback K scalarBits N bits pos hpos

theorem dataAndCallbackBitWork_eq {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (fallback : Fin k) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    l.dataAndCallbackBitWork model primitive fallback K scalarBits N bits pos hpos =
      (categoricalMachine fallback).cachedCallbackWork
        (fun state => categoricalCallbackBitCost model state +
          (categoricalMachine fallback).emissionCharge (l.decodedInterpolationBitCost model primitive K scalarBits) state)
        N bits (.state l.start) pos hpos := by
  unfold dataAndCallbackBitWork choiceCallbackBitWork decodedInterpolationWork WordStateMachine.cachedEmissionWork
  rw [machine, WordStateMachine.cachedCallbackWork_mapped, WordStateMachine.cachedCallbackWork_add]

theorem HeightAt.dataAndCallbackBitWork_bound {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (fallback : Fin k)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    l.dataAndCallbackBitWork model primitive fallback K scalarBits N bits pos hpos ≤
      k * (8 * k + 11) * model.rat (categoricalRequestWidth k s) +
        (3 * K + (4 + 2 * c) * K * binaryWordWidth K + c * (K + 2) +
          11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
            13 * n * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 3)) := by
  have hc := l.choiceCallbackBitWork_bound model fallback s h K scalarBits N bits pos hpos
  have he := h.decodedInterpolationWork_bound hs model primitive c hPrimitive fallback K scalarBits N bits pos hpos
  unfold dataAndCallbackBitWork
  omega

end Blotto.RationalSegmentLottery
