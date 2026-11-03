import Blotto.GeneralPaperEqualStaticCodeOwner

/-! The actual segment caller keeps original values/budget, rounded weights,
lengths, packed member lists/totals, prepared routes, fixed code and retained
prefix controls simultaneously. Each shared payload owner is counted once. -/
namespace Blotto.GeneralPaperEqualSegmentCallerOwners
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile)
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperEqualNativeSampler (rounded roundDen)
open GeneralPaperEqualFiniteKernel (terminal)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def controlFoot (A W n D exponent rawWork lengthWork packingWork routeWork : ℕ) : ℕ :=
  fields A [W, A, n, D, exponent, rawWork, lengthWork, packingWork, routeWork,
    rawWork + lengthWork, rawWork + lengthWork + packingWork,
    rawWork + lengthWork + packingWork + routeWork] + 512 * A

def controlProfile (A W n D exponent F : ℕ) : ℕ :=
  12 * (natBits (A + W + n + D + exponent + F + 1) + A) + 544 * A

theorem controls_bound (A W n D exponent rawWork lengthWork packingWork routeWork F : ℕ)
    (h : rawWork + lengthWork + packingWork + routeWork ≤ F) :
    controlFoot A W n D exponent rawWork lengthWork packingWork routeWork ≤ controlProfile A W n D exponent F := by
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (A + W + n + D + exponent + F + 1)
    [W, A, n, D, exponent, rawWork, lengthWork, packingWork, routeWork,
      rawWork + lengthWork, rawWork + lengthWork + packingWork,
      rawWork + lengthWork + packingWork + routeWork] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 12 * (natBits (A + W + n + D + exponent + F + 1) + A) + 32 * A at hFields
  unfold controlFoot controlProfile
  omega

def footprint {n : ℕ} {i : RationalTerminalLotto n} (A W exponent : ℕ) (values : FixedArrayTable n ℚ)
    (raw : FixedArrayTable n ℕ × ℕ) (lengths : FixedArrayTable n ℚ) (packed : RationalTerminalPacking i)
    (routes : PreparedGroupOutput i.partition) (budget : ℚ) (rawWork lengthWork packingWork routeWork : ℕ) : ℕ :=
  arrayFootprint A rationalWordWidth values + rationalWordWidth budget +
    GeneralPaperEqualPrefixOwners.roundedFoot A raw.1 raw.2 + arrayFootprint A rationalWordWidth lengths +
    GeneralPaperEqualPackedOwner.footprint A packed + GeneralPaperEqualRouteOwner.footprint A routes +
    GeneralPaperEqualStaticCodeOwner.footprint A + controlFoot A W n raw.2 exponent rawWork lengthWork packingWork routeWork

def profile (A W n exponent inputSize budgetSize D F : ℕ) : ℕ :=
  let s := binaryWordWidth n + exponent + 9
  inputSize + n * A + 64 * A + budgetSize +
    GeneralPaperEqualPrefixOwners.roundedProfile A n s + arrayProfile A n (1 + 2 * s) +
    GeneralPaperEqualPackedOwner.profile A n 3 s + GeneralPaperEqualRouteOwner.profile A n 3 s +
    GeneralPaperEqualStaticCodeOwner.profile A + controlProfile A W n D exponent F

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1)
    (packed : RationalTerminalPacking (terminal (rounded bits model W exponent values v hv) small))
    (lengths : FixedArrayTable n ℚ) (hLength : ∀ j, lengths.read j = (terminal (rounded bits model W exponent values v hv) small).length j)
    (routes : PreparedGroupOutput (terminal (rounded bits model W exponent values v hv) small).partition)
    (budget : ℚ) (rawWork lengthWork packingWork routeWork F : ℕ)
    (hWork : rawWork + lengthWork + packingWork + routeWork ≤ F) :
    footprint A W exponent values (GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values).1
      lengths packed routes budget rawWork lengthWork packingWork routeWork ≤
      profile A W n exponent (GeneralPaperValueRoundingInputPrice.inputSize values)
        (rationalWordWidth budget) (roundDen bits model W exponent values) F := by
  have hOriginal := GeneralPaperEqualPrefixOwners.original_exact A values
  have hRaw := GeneralPaperEqualPrefixOwners.native_rounded bits model W A exponent values v hv
  have hLengths := GeneralPaperEqualPrefixOwners.native_lengths bits model W A exponent values v hv small packed lengths hLength
  have hPacked := GeneralPaperEqualPackedOwner.native bits model W A exponent values v hv small packed lengths hLength
  have hRoutes := GeneralPaperEqualRouteOwner.native bits model W A exponent values v hv small routes
  have hCode := GeneralPaperEqualStaticCodeOwner.bounded A
  have hControls := controls_bound A W n (roundDen bits model W exponent values) exponent rawWork lengthWork packingWork routeWork F hWork
  unfold footprint profile
  dsimp only
  rw [hOriginal]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_left hRaw _) hLengths) hPacked) hRoutes) hCode) hControls

end Blotto.GeneralPaperEqualSegmentCallerOwners
