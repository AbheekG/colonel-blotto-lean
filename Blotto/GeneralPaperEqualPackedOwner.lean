import Blotto.GeneralPaperEqualPrefixOwners

/-! Packed-group ownership counts all member-list labels once across the
partition, together with cached totals and list/array references. No worst
case n-label allowance is multiplied by the number of groups. -/
namespace Blotto.GeneralPaperEqualPackedOwner
open scoped BigOperators
open GeneralPaperEncodedScalarStorage (natBits listFootprint list_bound)
open GeneralPaperEncodedBasisStorage (arrayFootprint)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def memberCount {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) : ℕ :=
  ∑ g, (p.groups.read g).1.length

theorem members_exact {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    memberCount p = i.uniformItems.length := by
  have h := congrArg List.length (GeneralPaperEqualRouteConstruction.members_eq_uniform p)
  rw [List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn] at h
  exact h

theorem members_le {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) : memberCount p ≤ n := by
  rw [members_exact]
  have h := List.length_filter_le (p := fun j => decide (i.resource j = i.length j)) (l := List.finRange n)
  simpa only [RationalTerminalLotto.uniformItems, List.length_finRange] using h

def entryFoot {n : ℕ} (A : ℕ) (entry : List (Fin n) × ℚ) : ℕ :=
  listFootprint A (fun j => natBits j.val) entry.1 + rationalWordWidth entry.2 + 32 * A

def footprint {n : ℕ} {i : RationalTerminalLotto n} (A : ℕ) (p : RationalTerminalPacking i) : ℕ :=
  arrayFootprint A (entryFoot A) p.groups + 32 * A

def profile (A n m s : ℕ) : ℕ :=
  n * (1 + binaryWordWidth n + 2 * A) + m * (1 + 2 * s + 65 * A) + 96 * A

theorem bounded {n : ℕ} {i : RationalTerminalLotto n} (A s : ℕ) (p : RationalTerminalPacking i)
    (hTotal : ∀ g, RationalHeight (p.groups.read g).2 s) :
    footprint A p ≤ profile A n i.groups.length s := by
  have hPoint (g : Fin i.groups.length) : A + entryFoot A (p.groups.read g) ≤
      (p.groups.read g).1.length * (1 + binaryWordWidth n + 2 * A) + (1 + 2 * s + 65 * A) := by
    have hList := list_bound A (1 + binaryWordWidth n) (fun j : Fin n => natBits j.val) (p.groups.read g).1 (by
      intro j _
      exact Nat.add_le_add_left (binaryWordWidth_mono j.isLt.le) 1)
    have hRat := rationalWordWidth_of_height (hTotal g)
    unfold entryFoot
    omega
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hPoint g)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hSum
  have hMembers := Nat.mul_le_mul_right (1 + binaryWordWidth n + 2 * A) (members_le p)
  unfold footprint arrayFootprint profile
  unfold memberCount at hMembers
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]
  nlinarith only [hSum, hMembers]

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small))
    (lengths : FixedArrayTable n ℚ)
    (hLength : ∀ j, lengths.read j = (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).length j) :
    footprint A p ≤ profile A n 3 (binaryWordWidth n + exponent + 9) := by
  have h := bounded A _ p ((GeneralPaperEqualNativeRouteCost.fields_height bits model W exponent values v hv small p lengths hLength).2)
  have hGroups := GeneralPaperEqualNativeCache.group_count (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small
  have hScale := Nat.mul_le_mul_right (1 + 2 * (binaryWordWidth n + exponent + 9) + 65 * A) hGroups
  unfold profile at h ⊢
  omega

end Blotto.GeneralPaperEqualPackedOwner
