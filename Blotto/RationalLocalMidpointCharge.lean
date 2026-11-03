import Blotto.RationalNestedMidpointLedger
import Blotto.CachedSerialReachedCharges
import Blotto.RationalFourCompleteDataCharge

/-! A per-callback midpoint metadata charge follows the same serial/binary
dispatch as the existing local data charge. Its value-independent bound holds
for every callback state, with source asks and nonemitting categorical states
paying zero. This supports enclosing four-variable/global composition. -/

namespace Blotto

theorem constantEmissionCharge_bound {S α : Type*} (m : WordStateMachine S α) (price bound : ℕ)
    (hPrice : price ≤ bound) (state : S) : m.emissionCharge (fun _ => price) state ≤ bound := by
  unfold WordStateMachine.emissionCharge
  cases h : m.step state with
  | done value => exact hPrice
  | ask a b hb hab upper lower => exact Nat.zero_le _

end Blotto
namespace Blotto.RationalNestedResourceSystem

def localMidpointMetadataCharge (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (cursor : i.SamplingState) : ℕ :=
  WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
    (fun value => (i.terminalData value).profileMidpointMetadataBitWork primitive K outerBits) cursor +
      WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
        (fun _ state => (categoricalMachine (0 : Fin 18)).emissionCharge
          (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits) state) cursor

theorem localMidpointMetadataCharge_bound (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (cursor : i.SamplingState) :
    i.localMidpointMetadataCharge primitive K outerBits scalarBits cursor ≤ 7 * dyadicMidpointMetadataBound c K := by
  have hScalar := dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K scalarBits
  have hEmit := constantEmissionCharge_bound (categoricalMachine (0 : Fin 18)) _ _ hScalar
  cases cursor with
  | source state =>
    unfold localMidpointMetadataCharge WordStateMachine.serialFactoryCharge WordStateMachine.serialHandoffCharge
    cases hStep : i.phase.step state with
    | ask a b hb hab upper lower => simp only [hStep, Nat.zero_add, Nat.zero_le]
    | done value =>
      have hPrice := (i.terminalData value).profileMidpointMetadataBitWork_bound primitive c hPrimitive K outerBits
      have hPoint := hEmit (i.continuationStart K outerBits value)
      simp only [hStep, Nat.zero_add]
      omega
  | continuation value state =>
    have hPrice := (i.terminalData value).profileMidpointMetadataBitWork_bound primitive c hPrimitive K outerBits
    have hPoint := hEmit state
    change (i.terminalData value).profileMidpointMetadataBitWork primitive K outerBits +
      (categoricalMachine (0 : Fin 18)).emissionCharge (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits) state ≤ _
    omega

end Blotto.RationalNestedResourceSystem
namespace Blotto.RationalFourInput

def smallMidpointMetadataCharge (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (primitive : ℕ → ℕ)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) : i.SmallState hcase → ℕ :=
  binaryCallbackCharge 0
    ((categoricalMachine (0 : Fin 9)).emissionCharge (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits))
    (fun cursor => 4 * (i.reflectedResourceSystem hcase).localMidpointMetadataCharge primitive K outerBits scalarBits cursor)

theorem smallMidpointMetadataCharge_bound (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (cursor : i.SmallState hcase) :
    i.smallMidpointMetadataCharge hcase primitive K outerBits scalarBits cursor ≤ 28 * dyadicMidpointMetadataBound c K := by
  cases cursor with
  | start => exact Nat.zero_le _
  | upper state =>
    exact (constantEmissionCharge_bound (categoricalMachine (0 : Fin 9)) _ _
      (dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K scalarBits) state).trans (by omega)
  | lower state =>
    have h := (i.reflectedResourceSystem hcase).localMidpointMetadataCharge_bound primitive c hPrimitive K outerBits scalarBits state
    change 4 * (i.reflectedResourceSystem hcase).localMidpointMetadataCharge primitive K outerBits scalarBits state ≤ _
    omega

def fourMidpointMetadataCharge (i : RationalFourInput) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : FourSamplingState i → ℕ
  | .gluing _ state => (categoricalMachine (0 : Fin 81)).emissionCharge (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits) state
  | .small hcase state => i.smallMidpointMetadataCharge hcase primitive K outerBits scalarBits state

theorem fourMidpointMetadataCharge_bound (i : RationalFourInput) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (cursor : FourSamplingState i) :
    i.fourMidpointMetadataCharge primitive K outerBits scalarBits cursor ≤ 28 * dyadicMidpointMetadataBound c K := by
  cases cursor with
  | small hcase state => exact i.smallMidpointMetadataCharge_bound hcase primitive c hPrimitive K outerBits scalarBits state
  | gluing hcase state =>
    exact (constantEmissionCharge_bound (categoricalMachine (0 : Fin 81)) _ _
      (dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K scalarBits) state).trans (by omega)

end Blotto.RationalFourInput
