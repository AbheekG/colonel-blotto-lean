import Blotto.GeneralPaperScalarCopyLifetimeMonotone

/-! Literal selected-copy child windows. Pure rows use their stored outer
reference and copy the chosen label; grouped children use their stored inner
reference. Typed cursors follow the actual selected branch. -/
namespace Blotto.GeneralPaperEqualSelectedCopyComponents
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage
open GeneralPaperEqualBitDrawRates (log)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def BranchCursor {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} :
    GeneralPaperEqualBitBranch.Prepared v k budget → Type
  | .dominant _ _ _ _ => Fin (n + 1)
  | .grouped _ sampler _ _ => GeneralPaperEqualNativeCopyLifetime.Cursor sampler

def Cursor {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) := BranchCursor a.branch

def window {n : ℕ} (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} :
    (branch : GeneralPaperEqualBitBranch.Prepared v k budget) → BranchCursor branch → ℕ
  | .dominant chosen _ row _,cursor =>
    GeneralPaperEqualPureCopyLifetime.window S A row cursor.val (by omega) +
      GeneralPaperScalarTableCopyLifetime.scalarWindow S A (fun j : Fin n => natBits j.val) chosen
  | .grouped _ sampler _ _,cursor => GeneralPaperEqualNativeCopyLifetime.window S sampler.address sampler cursor

def profile (S n k b : ℕ) : ℕ :=
  GeneralPaperEqualNativeCopyLifetime.profile S n k b +
    GeneralPaperScalarTableCopyLifetime.profile S (2 * log n k b + 1) n (3 * n + b) (b + 3) +
    GeneralPaperScalarTableCopyLifetime.scalarProfile S (2 * log n k b + 1) (natBits n)

theorem bounded {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (cursor : Cursor a) : window S a.address a.branch cursor ≤ profile S n k (rationalWordWidth budget) := by
  have hA := GeneralPaperEqualSelectedSampler.address_bound a
  cases a with
  | mk branch A hAddress =>
    dsimp only at hA ⊢
    cases branch with
    | dominant chosen heavy row correct =>
      change A = GeneralPaperEqualBitDrawRates.address n 0 k (rationalWordWidth budget) + 1 at hAddress
      have hRow := GeneralPaperEqualPureCopyLifetime.all_cursors S k budget chosen row correct cursor.val (by omega)
      dsimp only [GeneralPaperEqualPureCopyLifetime.profile] at hRow
      rw [← hAddress] at hRow
      have hRowMono := GeneralPaperScalarCopyLifetimeMonotone.table S n hA
        (le_rfl : 3 * n + rationalWordWidth budget ≤ 3 * n + rationalWordWidth budget)
        (le_rfl : rationalWordWidth budget + 3 ≤ rationalWordWidth budget + 3)
      have hi : natBits chosen.val ≤ natBits n := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
      have hLabel := GeneralPaperScalarTableCopyLifetime.scalar_bound S A (natBits n)
        (fun j : Fin n => natBits j.val) chosen hi
      have hLabelMono := GeneralPaperScalarCopyLifetimeMonotone.scalar S hA (le_rfl : natBits n ≤ natBits n)
      dsimp only [window,profile]
      omega
    | grouped small sampler hK hB =>
      have hs := GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hB
      subst sampler
      have hGroup := GeneralPaperEqualNativeCopyLifetime.native model W S k values v hv small budget cursor
      dsimp only [GeneralPaperEqualStoredBitSampler.native,GeneralPaperEqualNativeCache.prepare] at hGroup
      dsimp only [window,profile]
      omega

end Blotto.GeneralPaperEqualSelectedCopyComponents
