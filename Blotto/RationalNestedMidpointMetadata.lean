import Blotto.DyadicMidpointMetadataWork
import Blotto.RationalTerminalResourcePreparation
import Blotto.RationalNestedFactoryWork

/-! Midpoint metadata follows the existing ordered profile and endpoint
branches. The terminal wrapper retains the same conservative three child
prices as its preparation ledger. Repeated serial factories are then charged
on the actual indexed continuation, without assuming factory caching. -/

namespace Blotto.RationalNestedInput

def profileMidpointMetadataBitWork (i : RationalNestedInput) (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  if i.t ≤ i.v then dyadicMidpointMetadataBitWork primitive K bits else
    if i.u ≤ i.t then dyadicMidpointMetadataBitWork primitive K bits else
      if 0 < i.v then dyadicMidpointMetadataBitWork primitive K bits else 0

theorem profileMidpointMetadataBitWork_bound (i : RationalNestedInput) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    i.profileMidpointMetadataBitWork primitive K bits ≤ dyadicMidpointMetadataBound c K := by
  have h := dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K bits
  unfold profileMidpointMetadataBitWork
  split_ifs <;> omega

end Blotto.RationalNestedInput
namespace Blotto.RationalNestedSpec

def profileMidpointMetadataBitWork (i : RationalNestedSpec) (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  if hq0 : i.q = 0 then 0 else if hq1 : i.q = 1 then 0 else
    (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).profileMidpointMetadataBitWork primitive K bits

theorem profileMidpointMetadataBitWork_bound (i : RationalNestedSpec) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    i.profileMidpointMetadataBitWork primitive K bits ≤ dyadicMidpointMetadataBound c K := by
  unfold profileMidpointMetadataBitWork
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · apply RationalNestedInput.profileMidpointMetadataBitWork_bound
      exact hPrimitive

end Blotto.RationalNestedSpec
namespace Blotto.RationalTerminalResources

def profileMidpointMetadataBitWork (i : RationalTerminalResources) (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  3 * i.input.profileMidpointMetadataBitWork primitive K bits

theorem profileMidpointMetadataBitWork_bound (i : RationalTerminalResources) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    i.profileMidpointMetadataBitWork primitive K bits ≤ 3 * dyadicMidpointMetadataBound c K :=
  Nat.mul_le_mul_left 3 (i.input.profileMidpointMetadataBitWork_bound primitive c hPrimitive K bits)

end Blotto.RationalTerminalResources
namespace Blotto.RationalNestedResourceSystem

def terminalProfileMidpointMetadataBitWork (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
      (fun value => (i.terminalData value).profileMidpointMetadataBitWork primitive K outerBits))
    N bits (.state i.samplingStart) pos hpos

theorem terminalProfileMidpointMetadataBitWork_bound (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalProfileMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos ≤
      57 * dyadicMidpointMetadataBound c K := by
  unfold terminalProfileMidpointMetadataBitWork machine samplingStart
  have h := i.phase.cachedSerialFactoryWork_bound_under (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    (fun _ => True) (fun _ => True)
    (fun state _ => by cases hs : i.phase.step state <;> simp [WordTransition.Postcondition])
    (fun value => (i.terminalData value).profileMidpointMetadataBitWork primitive K outerBits)
    (3 * dyadicMidpointMetadataBound c K)
    (fun value _ => (i.terminalData value).profileMidpointMetadataBitWork_bound primitive c hPrimitive K outerBits)
    N bits i.start trivial pos hpos
  have hConstant : (3 * dyadicMidpointMetadataBound c K) * (17 + 2) = 57 * dyadicMidpointMetadataBound c K := by ring
  exact h.trans_eq hConstant

end Blotto.RationalNestedResourceSystem
