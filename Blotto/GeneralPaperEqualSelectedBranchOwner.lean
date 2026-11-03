import Blotto.GeneralPaperEqualSelectedContract

/-! Actual selected-branch ownership at the preparation reference width.
Pure payload sums the sole original budget once. Grouped ownership includes
the full rational/Boolean cache and every stored control. The bound does not
perform a draw-reference re-encoding or an allocation census. -/
namespace Blotto.GeneralPaperEqualSelectedBranchOwner
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def footprint {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (W : ℕ) :
    GeneralPaperEqualBitBranch.Prepared v k budget → ℕ
  | .dominant chosen _ row _ => arrayFootprint W rationalWordWidth (⟨row.data,row.size⟩ : FixedArrayTable n ℚ) +
      natBits chosen.val + 32 * W
  | .grouped _ sampler _ _ => GeneralPaperEqualRetainedStorage.footprint W sampler

def pureProfile (W n b : ℕ) : ℕ := 3 * n + b + n * W + 96 * W + natBits n
def profile (W n k b : ℕ) : ℕ := GeneralPaperEqualNativeRetainedStorage.profile W n k b + pureProfile W n b

theorem pure_bound {n : ℕ} (W : ℕ) (budget : ℚ) (chosen : Fin n) (row : RationalResourceArray n)
    (h : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen) :
    arrayFootprint W rationalWordWidth (⟨row.data,row.size⟩ : FixedArrayTable n ℚ) + natBits chosen.val + 32 * W ≤
      pureProfile W n (rationalWordWidth budget) := by
  have hp : (∑ j : Fin n, rationalWordWidth (row.allocation j)) ≤ 3 * n + rationalWordWidth budget := by
    simp_rw [GeneralPaperEqualBitCanonical.pure_coordinates budget chosen row h]
    exact GeneralPaperEqualBitVertex.payload budget chosen
  have hi : natBits chosen.val ≤ natBits n := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  change 64 * W + (∑ j : Fin n, (W + rationalWordWidth (row.allocation j))) + natBits chosen.val + 32 * W ≤ _
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  unfold pureProfile
  omega

theorem bounded {n : ℕ} (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (p : GeneralPaperEqualBitBranch.Prepared
      (GeneralPaperEqualNativeSampler.rounded true model Wv k values v hv) k budget) :
    footprint W p ≤ profile W n k (rationalWordWidth budget) := by
  cases p with
  | dominant chosen heavy row correct =>
    exact (pure_bound W budget chosen row correct).trans (Nat.le_add_left _ _)
  | grouped small sampler hK hB =>
    have hs := GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hB
    subst sampler
    exact (GeneralPaperEqualNativeRetainedStorage.native_bound true model Wv W k values v hv small budget).trans
      (Nat.le_add_right _ _)

end Blotto.GeneralPaperEqualSelectedBranchOwner
