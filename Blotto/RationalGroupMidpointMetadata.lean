import Blotto.RationalFourMidpointMetadata
import Blotto.RationalTerminalGroupCompleteProcessing
import Blotto.CachedEmissionWork

/-! Terminal group dispatch carries midpoint metadata on its actual uniform/
mixed branches. Two-group programs decode once on emission; three-group mixed
programs use the unsorted four-variable ledger at the original reader position. -/

namespace Blotto.RationalUniformGroupSpec

def midpointMetadataBitWork {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.program hm K scalarBits).machine.cachedEmissionWork (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits)
    N bits (.state (i.program hm K scalarBits).start) pos hpos

theorem midpointMetadataBitWork_bound {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.midpointMetadataBitWork hm primitive K scalarBits N bits pos hpos ≤ dyadicMidpointMetadataBound c K := by
  unfold midpointMetadataBitWork
  rw [WordStateMachine.cachedEmissionWork_eq]
  cases h : ((i.program hm K scalarBits).machine.runCachedIndexed N bits (.state (i.program hm K scalarBits).start) pos hpos).1 with
  | none => exact Nat.zero_le _
  | some output => exact dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K scalarBits

end Blotto.RationalUniformGroupSpec
namespace Blotto.RationalMixedGroupSpec

def midpointMetadataBitWork {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ := by
  by_cases h2 : m = 2
  · subst m
    exact (i.threeInput.segmentLottery.machine 0 K scalarBits).cachedEmissionWork
      (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits) N bits (.state i.threeInput.segmentLottery.start) pos hpos
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.midpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos

theorem midpointMetadataBitWork_bound {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.midpointMetadataBitWork hm primitive K outerBits scalarBits N bits pos hpos ≤ 9072 * dyadicMidpointMetadataBound c K := by
  rcases hm with rfl | rfl
  · change (i.threeInput.segmentLottery.machine 0 K scalarBits).cachedEmissionWork
      (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits) N bits (.state i.threeInput.segmentLottery.start) pos hpos ≤ _
    rw [WordStateMachine.cachedEmissionWork_eq]
    cases h : ((i.threeInput.segmentLottery.machine 0 K scalarBits).runCachedIndexed N bits (.state i.threeInput.segmentLottery.start) pos hpos).1 with
    | none => exact Nat.zero_le _
    | some output => exact (dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K scalarBits).trans (by omega)
  · exact i.fourInput.midpointMetadataBitWork_bound primitive c hPrimitive K outerBits scalarBits N bits pos hpos

end Blotto.RationalMixedGroupSpec
namespace Blotto.RationalTerminalLotto

def midpointMetadataBitWork {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let packed := RationalTerminalPacking.prepare i
  match h : i.pivot with
  | none => (packed.uniformSpec (i.pivot_none h)).midpointMetadataBitWork i.groups_count primitive K scalarBits N bits pos hpos
  | some pivot => (packed.mixedSpec pivot (i.pivot_some h)).midpointMetadataBitWork i.groups_count primitive K outerBits scalarBits N bits pos hpos

theorem midpointMetadataBitWork_bound {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.midpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos ≤ 9072 * dyadicMidpointMetadataBound c K := by
  unfold midpointMetadataBitWork
  dsimp only
  split
  · rename_i hNone
    exact ((RationalTerminalPacking.prepare i).uniformSpec (i.pivot_none hNone)).midpointMetadataBitWork_bound
      i.groups_count primitive c hPrimitive K scalarBits N bits pos hpos |>.trans (by omega)
  · rename_i pivot hSome
    exact ((RationalTerminalPacking.prepare i).mixedSpec pivot (i.pivot_some hSome)).midpointMetadataBitWork_bound
      i.groups_count primitive c hPrimitive K outerBits scalarBits N bits pos hpos

end Blotto.RationalTerminalLotto
