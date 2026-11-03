import Blotto.RationalScalarUseCharge
import Blotto.RationalGroupMidpointMetadata

/-! Arbitrary outer/scalar invocation prices accumulate through ordered
four-variable and terminal-group programs at the actual reader position.
This reuses factory/producer multiplicities, not output-equivalence timing. -/

namespace Blotto.RationalFourInput

def scalarUseWork (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (outerPrice scalarPrice : ℕ)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork (i.fourScalarUseCharge K outerBits outerPrice scalarPrice)
    N bits (.state (i.start K outerBits scalarBits)) pos hpos

theorem scalarUseWork_bound (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (outerPrice scalarPrice bound : ℕ) (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.scalarUseWork K outerBits scalarBits outerPrice scalarPrice N bits pos hpos ≤ 2268 * bound := by
  have h := (i.machine K outerBits scalarBits).cachedCallbackWork_state_bound
    (i.fourScalarUseCharge K outerBits outerPrice scalarPrice) (28 * bound)
    (i.fourScalarUseCharge_bound K outerBits outerPrice scalarPrice bound hOuter hScalar)
    N bits (i.start K outerBits scalarBits) pos hpos
  have hRank : (i.machine K outerBits scalarBits).rank (i.start K outerBits scalarBits) + 1 ≤ 81 := by
    have h := i.machine_rank K outerBits scalarBits
    omega
  have hPrice := h.trans (Nat.mul_le_mul_left (28 * bound) hRank)
  have hConstant : (28 * bound) * 81 = 2268 * bound := by ring
  exact hPrice.trans_eq hConstant

end Blotto.RationalFourInput
namespace Blotto.RationalFourSpec

def scalarUseWork (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (outerPrice scalarPrice : ℕ)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  4 * i.input.scalarUseWork K outerBits scalarBits outerPrice scalarPrice N bits pos hpos

theorem scalarUseWork_bound (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (outerPrice scalarPrice bound : ℕ) (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.scalarUseWork K outerBits scalarBits outerPrice scalarPrice N bits pos hpos ≤ 9072 * bound := by
  have h := Nat.mul_le_mul_left 4 (i.input.scalarUseWork_bound K outerBits scalarBits outerPrice scalarPrice bound hOuter hScalar N bits pos hpos)
  have hConstant : 4 * (2268 * bound) = 9072 * bound := by ring
  exact h.trans_eq hConstant

end Blotto.RationalFourSpec
namespace Blotto.RationalUniformGroupSpec

def scalarUseWork {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ)
    (scalarBits : Fin K → Bool) (scalarPrice : ℕ) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.program hm K scalarBits).machine.cachedEmissionWork (fun _ => scalarPrice)
    N bits (.state (i.program hm K scalarBits).start) pos hpos

theorem scalarUseWork_bound {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ)
    (scalarBits : Fin K → Bool) (scalarPrice bound : ℕ) (hScalar : scalarPrice ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.scalarUseWork hm K scalarBits scalarPrice N bits pos hpos ≤ bound := by
  unfold scalarUseWork
  rw [WordStateMachine.cachedEmissionWork_eq]
  cases h : ((i.program hm K scalarBits).machine.runCachedIndexed N bits (.state (i.program hm K scalarBits).start) pos hpos).1 with
  | none => exact Nat.zero_le _
  | some output => exact hScalar

end Blotto.RationalUniformGroupSpec
namespace Blotto.RationalMixedGroupSpec

def scalarUseWork {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (outerPrice scalarPrice : ℕ)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ := by
  by_cases h2 : m = 2
  · subst m
    exact (i.threeInput.segmentLottery.machine 0 K scalarBits).cachedEmissionWork (fun _ => scalarPrice)
      N bits (.state i.threeInput.segmentLottery.start) pos hpos
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.scalarUseWork K outerBits scalarBits outerPrice scalarPrice N bits pos hpos

theorem scalarUseWork_bound {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (outerPrice scalarPrice bound : ℕ)
    (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.scalarUseWork hm K outerBits scalarBits outerPrice scalarPrice N bits pos hpos ≤ 9072 * bound := by
  rcases hm with rfl | rfl
  · change (i.threeInput.segmentLottery.machine 0 K scalarBits).cachedEmissionWork (fun _ => scalarPrice)
      N bits (.state i.threeInput.segmentLottery.start) pos hpos ≤ _
    rw [WordStateMachine.cachedEmissionWork_eq]
    cases h : ((i.threeInput.segmentLottery.machine 0 K scalarBits).runCachedIndexed N bits (.state i.threeInput.segmentLottery.start) pos hpos).1 with
    | none => exact Nat.zero_le _
    | some output => exact hScalar.trans (by omega)
  · exact i.fourInput.scalarUseWork_bound K outerBits scalarBits outerPrice scalarPrice bound hOuter hScalar N bits pos hpos

end Blotto.RationalMixedGroupSpec
namespace Blotto.RationalTerminalLotto

def scalarUseWork {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (outerPrice scalarPrice : ℕ) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let packed := RationalTerminalPacking.prepare i
  match h : i.pivot with
  | none => (packed.uniformSpec (i.pivot_none h)).scalarUseWork i.groups_count K scalarBits scalarPrice N bits pos hpos
  | some pivot => (packed.mixedSpec pivot (i.pivot_some h)).scalarUseWork i.groups_count K outerBits scalarBits outerPrice scalarPrice N bits pos hpos

theorem scalarUseWork_bound {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (outerPrice scalarPrice bound : ℕ) (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.scalarUseWork K outerBits scalarBits outerPrice scalarPrice N bits pos hpos ≤ 9072 * bound := by
  unfold scalarUseWork
  dsimp only
  split
  · rename_i hNone
    exact ((RationalTerminalPacking.prepare i).uniformSpec (i.pivot_none hNone)).scalarUseWork_bound
      i.groups_count K scalarBits scalarPrice bound hScalar N bits pos hpos |>.trans (by omega)
  · rename_i pivot hSome
    exact ((RationalTerminalPacking.prepare i).mixedSpec pivot (i.pivot_some hSome)).scalarUseWork_bound
      i.groups_count K outerBits scalarBits outerPrice scalarPrice bound hOuter hScalar N bits pos hpos

end Blotto.RationalTerminalLotto
