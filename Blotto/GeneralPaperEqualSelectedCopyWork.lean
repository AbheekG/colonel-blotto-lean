import Blotto.GeneralPaperEqualNativeCopyWork

/-! Concrete native majorant for the actual selected copy, including every
source read, target write, scalar/tag/header and nested grouped field. The
pure row uses a sum of payload lengths, preserving additive budget precision. -/
namespace Blotto.GeneralPaperEqualSelectedCopyWork
open GeneralPaperEqualBitDrawRates (log)
open GeneralPaperEncodedScalarStorage (natBits)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

theorem pure {n : ℕ} (S A : ℕ) (budget : ℚ) (chosen : Fin n) (source : RationalResourceArray n)
    (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen) :
    (GeneralPaperEqualSelectedCopy.row S A source).2 ≤
      GeneralPaperScalarTableCopy.price S A n (3 * n + rationalWordWidth budget) + 64 * (S + A + 1) := by
  have hp : (∑ j : Fin n,rationalWordWidth (source.allocation j)) ≤ 3 * n + rationalWordWidth budget := by
    simp_rw [GeneralPaperEqualBitCanonical.pure_coordinates budget chosen source correct]
    exact GeneralPaperEqualBitVertex.payload budget chosen
  have h := GeneralPaperScalarTableCopy.work S A (3 * n + rationalWordWidth budget) rationalWordWidth
    (⟨source.data,source.size⟩ : FixedArrayTable n ℚ) hp
  dsimp only [GeneralPaperEqualSelectedCopy.row]
  omega

def profile (S n k b : ℕ) : ℕ :=
  GeneralPaperEqualNativeCopyWork.profile S n k b +
    GeneralPaperScalarTableCopy.price S (2 * log n k b + 1) n (3 * n + b) +
    natBits n + natBits (2 * log n k b + 1) + 512 * (S + 2 * log n k b + 2)

theorem work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : GeneralPaperEqualSelectedSampler.Sampler
      (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (GeneralPaperEqualSelectedCopy.run S a).2 ≤ profile S n k (rationalWordWidth budget) := by
  have hA := GeneralPaperEqualSelectedSampler.address_bound a
  cases a with
  | mk branch A hAddress =>
    dsimp only at hA ⊢
    have hBits : natBits A ≤ natBits (2 * log n k (rationalWordWidth budget) + 1) :=
      Nat.add_le_add_left (binaryWordWidth_mono hA) 1
    cases branch with
    | dominant chosen heavy source correct =>
      have hp := pure S A budget chosen source correct
      have hm := GeneralPaperEqualCopyPriceMonotone.scalar_target S n (3 * n + rationalWordWidth budget) hA
      have hi : natBits chosen.val ≤ natBits n := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
      dsimp only [GeneralPaperEqualSelectedCopy.run,GeneralPaperEqualSelectedCopy.branch,
        GeneralPaperReferenceCopy.scalar,profile]
      omega
    | grouped small sampler hK hB =>
      have hs := GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hB
      subst sampler
      have hg := GeneralPaperEqualNativeCopyWork.native model W S k values v hv small budget
      dsimp only [GeneralPaperEqualStoredBitSampler.native,GeneralPaperEqualNativeCache.prepare] at hg
      dsimp only [GeneralPaperEqualSelectedCopy.run,GeneralPaperEqualSelectedCopy.branch,
        GeneralPaperReferenceCopy.scalar,profile]
      omega

end Blotto.GeneralPaperEqualSelectedCopyWork
