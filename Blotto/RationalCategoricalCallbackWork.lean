import Blotto.RationalCategoricalBitPrice
import Blotto.CachedCallbackBounds
import Blotto.RationalSegmentMachine

/-! Categorical arithmetic and finite-binary callback prices accumulate on
the indexed native path. The caller's cap and current position are retained.
Descriptor construction, interpolation/emission and Boolean control are separate. -/

namespace Blotto

def categoricalCallbackArithmeticWork {α : Type*} : CategoricalState α → ℕ
  | .selected _ => 0
  | .remaining l => match l.items with
    | [] => 0
    | [_] => 0
    | _ :: _ :: _ => l.items.length + 1 + if 0 < l.mass then l.items.length + 1 else 0

theorem categoricalCallbackArithmeticWork_bound {α : Type*} (cursor : CategoricalState α) (k s : ℕ)
    (h : cursor.Bounded k s) : categoricalCallbackArithmeticWork cursor ≤ 2 * k + 2 := by
  cases cursor with
  | selected value => exact Nat.zero_le _
  | remaining l =>
    have hLen := h.1
    cases hi : l.items with
    | nil => simp only [categoricalCallbackArithmeticWork, hi]; omega
    | cons head rest =>
      cases hr : rest with
      | nil => simp only [categoricalCallbackArithmeticWork, hi, hr]; omega
      | cons next tail =>
        simp only [categoricalCallbackArithmeticWork, hi, hr]
        rw [hi, hr] at hLen
        split_ifs <;> omega

theorem categoricalCallbackWork_bound {α : Type*} (fallback : α) (charge : CategoricalState α → ℕ)
    (bound k s : ℕ) (hk : 0 < k) (hCharge : ∀ cursor, cursor.Bounded k s → charge cursor ≤ bound)
    (l : RationalWeightList α) (hL : l.Bounded k s) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (categoricalMachine fallback).cachedCallbackWork charge N bits (.state (.remaining l)) pos hpos ≤ k * bound := by
  have h := (categoricalMachine fallback).cachedCallbackWork_state_bound_under
    (fun cursor => cursor.Bounded k s) (categoricalTransition_bounded fallback k s)
    charge bound hCharge N bits (.remaining l) hL pos hpos
  have hRank : (categoricalMachine fallback).rank (.remaining l) + 1 ≤ k := by
    change l.items.length - 1 + 1 ≤ k
    have hLen := hL.1
    omega
  have hMul := Nat.mul_le_mul_left bound hRank
  exact h.trans (hMul.trans_eq (Nat.mul_comm bound k))

theorem categoricalCallbackBitWork_bound {α : Type*} (fallback : α) (model : RationalCostModel)
    (l : RationalWeightList α) (k s : ℕ) (hk : 0 < k) (hL : l.Bounded k s)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (categoricalMachine fallback).cachedCallbackWork (categoricalCallbackBitCost model)
      N bits (.state (.remaining l)) pos hpos ≤ k * (8 * k + 11) * model.rat (categoricalRequestWidth k s) := by
  have h := categoricalCallbackWork_bound fallback (categoricalCallbackBitCost model)
    ((8 * k + 11) * model.rat (categoricalRequestWidth k s)) k s hk
    (fun cursor hCursor => categoricalCallbackBitCost_bound model cursor k s hCursor) l hL N bits pos hpos
  simpa only [Nat.mul_assoc] using h

theorem categoricalCallbackArithmeticTotal_bound {α : Type*} (fallback : α)
    (l : RationalWeightList α) (k s : ℕ) (hk : 0 < k) (hL : l.Bounded k s)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (categoricalMachine fallback).cachedCallbackWork categoricalCallbackArithmeticWork
      N bits (.state (.remaining l)) pos hpos ≤ k * (2 * k + 2) :=
  categoricalCallbackWork_bound fallback categoricalCallbackArithmeticWork (2 * k + 2) k s hk
    (fun cursor hCursor => categoricalCallbackArithmeticWork_bound cursor k s hCursor) l hL N bits pos hpos

end Blotto
namespace Blotto.RationalSegmentLottery

def choiceCallbackBitWork {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (fallback : Fin k) (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool)
    (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (l.machine fallback K scalarBits).cachedCallbackWork (categoricalCallbackBitCost model)
    N bits (.state l.start) pos hpos

theorem choiceCallbackBitWork_bound {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (fallback : Fin k) (s : ℕ) (h : l.HeightAt s) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    l.choiceCallbackBitWork model fallback K scalarBits N bits pos hpos ≤
      k * (8 * k + 11) * model.rat (categoricalRequestWidth k s) := by
  have hk : 0 < k := by have hf := fallback.isLt; omega
  rw [choiceCallbackBitWork, machine, WordStateMachine.cachedCallbackWork_mapped]
  exact categoricalCallbackBitWork_bound fallback model (rationalWeightList l.weight l.nonnegative) k s hk
    (rationalWeightList_bounded l.weight l.nonnegative s h.1) N bits pos hpos

theorem choiceCallbackArithmeticWork_bound {n k : ℕ} (l : RationalSegmentLottery n k)
    (fallback : Fin k) (s : ℕ) (h : l.HeightAt s) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (l.machine fallback K scalarBits).cachedCallbackWork categoricalCallbackArithmeticWork
      N bits (.state l.start) pos hpos ≤ k * (2 * k + 2) := by
  have hk : 0 < k := by have hf := fallback.isLt; omega
  rw [machine, WordStateMachine.cachedCallbackWork_mapped]
  exact categoricalCallbackArithmeticTotal_bound fallback (rationalWeightList l.weight l.nonnegative) k s hk
    (rationalWeightList_bounded l.weight l.nonnegative s h.1) N bits pos hpos

end Blotto.RationalSegmentLottery
