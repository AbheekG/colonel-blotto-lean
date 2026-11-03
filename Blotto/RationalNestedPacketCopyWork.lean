import Blotto.RationalNestedFactoryWork

/-! A terminal packet has ten rational scalar fields. Read/write copies are
allowed conservatively for each machine/start factory invocation; pointer,
tag/list, allocation and physical reference ownership are separate. -/

namespace Blotto.RationalTerminalResources
open scoped BigOperators

def scalarPayloadBitCost (i : RationalTerminalResources) : ℕ :=
  rationalWordWidth i.M + (∑ j, rationalWordWidth (i.long j)) +
    (∑ j, rationalWordWidth (i.short j)) + ∑ j, rationalWordWidth (i.resource j)

theorem FieldsHeight.scalarPayloadBitCost_bound {i : RationalTerminalResources} {s : ℕ}
    (h : i.FieldsHeight s) (model : RationalCostModel) :
    i.scalarPayloadBitCost ≤ 10 * model.rat (1 + 2 * s) := by
  have hM := (rationalWordWidth_of_height h.1).trans (model.word_le _)
  have hLong : (∑ j : Fin 3, rationalWordWidth (i.long j)) ≤ 3 * model.rat (1 + 2 * s) := by
    calc
      _ ≤ ∑ _j : Fin 3, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (h.2.1 j)).trans (model.word_le _))
      _ = _ := by simp
  have hShort : (∑ j : Fin 3, rationalWordWidth (i.short j)) ≤ 3 * model.rat (1 + 2 * s) := by
    calc
      _ ≤ ∑ _j : Fin 3, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (h.2.2.1 j)).trans (model.word_le _))
      _ = _ := by simp
  have hResource : (∑ j : Fin 3, rationalWordWidth (i.resource j)) ≤ 3 * model.rat (1 + 2 * s) := by
    calc
      _ ≤ ∑ _j : Fin 3, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (h.2.2.2 j)).trans (model.word_le _))
      _ = _ := by simp
  unfold scalarPayloadBitCost
  omega

end Blotto.RationalTerminalResources
namespace Blotto.RationalNestedResourceSystem

def terminalPacketCopyPrice (i : RationalNestedResourceSystem) (value : i.PhaseResult) : ℕ :=
  2 * (i.terminalData value).scalarPayloadBitCost

theorem FieldsHeight.terminalPacketCopyPrice_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (model : RationalCostModel) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) :
    i.terminalPacketCopyPrice value ≤ 20 * model.rat (1 + 2 * expressionHeightBudget s 7) := by
  have hp := (h.terminalData value hValue).scalarPayloadBitCost_bound model
  unfold terminalPacketCopyPrice
  omega

def terminalPacketCopyBitWork (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits) i.terminalPacketCopyPrice)
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.terminalPacketCopyBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalPacketCopyBitWork K outerBits scalarBits N bits pos hpos ≤
      380 * model.rat (1 + 2 * expressionHeightBudget s 7) := by
  unfold terminalPacketCopyBitWork machine samplingStart
  have hp := i.phase.cachedSerialFactoryWork_bound_under (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7)) (h.localHeight_closed hs)
    i.terminalPacketCopyPrice (20 * model.rat (1 + 2 * expressionHeightBudget s 7))
    (fun value hValue => h.terminalPacketCopyPrice_bound model value hValue)
    N bits i.start h.localHeight_start pos hpos
  have he : 20 * model.rat (1 + 2 * expressionHeightBudget s 7) * (17 + 2) =
      380 * model.rat (1 + 2 * expressionHeightBudget s 7) := by ring
  exact hp.trans_eq he

end Blotto.RationalNestedResourceSystem
