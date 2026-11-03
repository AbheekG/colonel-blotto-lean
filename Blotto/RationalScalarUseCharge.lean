import Blotto.RationalLocalMidpointCharge

/-! Value-independent prices for actual outer/scalar block invocations.
The branch and factory structure matches midpoint construction: endpoint
profiles use no outer block, interior profiles may use one, and the terminal
wrapper retains three uncached child prices. Prices can count calls or reads. -/

namespace Blotto.RationalNestedInput

def profileScalarUsePrice (i : RationalNestedInput) (price : ℕ) : ℕ :=
  if i.t ≤ i.v then price else if i.u ≤ i.t then price else if 0 < i.v then price else 0

theorem profileScalarUsePrice_bound (i : RationalNestedInput) (price : ℕ) : i.profileScalarUsePrice price ≤ price := by
  unfold profileScalarUsePrice
  split_ifs <;> omega

end Blotto.RationalNestedInput
namespace Blotto.RationalNestedSpec

def profileScalarUsePrice (i : RationalNestedSpec) (price : ℕ) : ℕ :=
  if hq0 : i.q = 0 then 0 else if hq1 : i.q = 1 then 0 else
    (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).profileScalarUsePrice price

theorem profileScalarUsePrice_bound (i : RationalNestedSpec) (price : ℕ) : i.profileScalarUsePrice price ≤ price := by
  unfold profileScalarUsePrice
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact RationalNestedInput.profileScalarUsePrice_bound _ price

end Blotto.RationalNestedSpec
namespace Blotto.RationalTerminalResources

def profileScalarUsePrice (i : RationalTerminalResources) (price : ℕ) : ℕ := 3 * i.input.profileScalarUsePrice price

theorem profileScalarUsePrice_bound (i : RationalTerminalResources) (price : ℕ) : i.profileScalarUsePrice price ≤ 3 * price :=
  Nat.mul_le_mul_left 3 (i.input.profileScalarUsePrice_bound price)

end Blotto.RationalTerminalResources
namespace Blotto.RationalNestedResourceSystem

def scalarUseCharge (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool)
    (outerPrice scalarPrice : ℕ) (cursor : i.SamplingState) : ℕ :=
  WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
    (fun value => (i.terminalData value).profileScalarUsePrice outerPrice) cursor +
      WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
        (fun _ state => (categoricalMachine (0 : Fin 18)).emissionCharge (fun _ => scalarPrice) state) cursor

theorem scalarUseCharge_bound (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool)
    (outerPrice scalarPrice bound : ℕ) (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound) (cursor : i.SamplingState) :
    i.scalarUseCharge K outerBits outerPrice scalarPrice cursor ≤ 7 * bound := by
  have hEmit := constantEmissionCharge_bound (categoricalMachine (0 : Fin 18)) scalarPrice bound hScalar
  cases cursor with
  | source state =>
    unfold scalarUseCharge WordStateMachine.serialFactoryCharge WordStateMachine.serialHandoffCharge
    cases hStep : i.phase.step state with
    | ask a b hb hab upper lower => simp only [hStep, Nat.zero_add, Nat.zero_le]
    | done value =>
      have hPrice := (i.terminalData value).profileScalarUsePrice_bound outerPrice
      have hPoint := hEmit (i.continuationStart K outerBits value)
      simp only [hStep, Nat.zero_add]
      omega
  | continuation value state =>
    have hPrice := (i.terminalData value).profileScalarUsePrice_bound outerPrice
    have hPoint := hEmit state
    change (i.terminalData value).profileScalarUsePrice outerPrice +
      (categoricalMachine (0 : Fin 18)).emissionCharge (fun _ => scalarPrice) state ≤ _
    omega

end Blotto.RationalNestedResourceSystem
namespace Blotto.RationalFourInput

def smallScalarUseCharge (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (outerBits : Fin K → Bool)
    (outerPrice scalarPrice : ℕ) : i.SmallState hcase → ℕ :=
  binaryCallbackCharge 0 ((categoricalMachine (0 : Fin 9)).emissionCharge (fun _ => scalarPrice))
    (fun cursor => 4 * (i.reflectedResourceSystem hcase).scalarUseCharge K outerBits outerPrice scalarPrice cursor)

theorem smallScalarUseCharge_bound (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (outerBits : Fin K → Bool)
    (outerPrice scalarPrice bound : ℕ) (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound) (cursor : i.SmallState hcase) :
    i.smallScalarUseCharge hcase K outerBits outerPrice scalarPrice cursor ≤ 28 * bound := by
  cases cursor with
  | start => exact Nat.zero_le _
  | upper state => exact (constantEmissionCharge_bound (categoricalMachine (0 : Fin 9)) scalarPrice bound hScalar state).trans (by omega)
  | lower state =>
    have h := (i.reflectedResourceSystem hcase).scalarUseCharge_bound K outerBits outerPrice scalarPrice bound hOuter hScalar state
    change 4 * (i.reflectedResourceSystem hcase).scalarUseCharge K outerBits outerPrice scalarPrice state ≤ _
    omega

def fourScalarUseCharge (i : RationalFourInput) (K : ℕ) (outerBits : Fin K → Bool)
    (outerPrice scalarPrice : ℕ) : FourSamplingState i → ℕ
  | .gluing _ state => (categoricalMachine (0 : Fin 81)).emissionCharge (fun _ => scalarPrice) state
  | .small hcase state => i.smallScalarUseCharge hcase K outerBits outerPrice scalarPrice state

theorem fourScalarUseCharge_bound (i : RationalFourInput) (K : ℕ) (outerBits : Fin K → Bool)
    (outerPrice scalarPrice bound : ℕ) (hOuter : outerPrice ≤ bound) (hScalar : scalarPrice ≤ bound) (cursor : FourSamplingState i) :
    i.fourScalarUseCharge K outerBits outerPrice scalarPrice cursor ≤ 28 * bound := by
  cases cursor with
  | small hcase state => exact i.smallScalarUseCharge_bound hcase K outerBits outerPrice scalarPrice bound hOuter hScalar state
  | gluing hcase state => exact (constantEmissionCharge_bound (categoricalMachine (0 : Fin 81)) scalarPrice bound hScalar state).trans (by omega)

end Blotto.RationalFourInput
