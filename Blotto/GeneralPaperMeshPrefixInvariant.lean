import Blotto.GeneralPaperMeshQueryMetadata

/-! Constructed cached prefixes supply a positive whole-block denominator,
bounded prefix reads and the derived total word. No online scan is used.
-/
namespace Blotto.GeneralPaperMeshPrefixInvariant
open scoped BigOperators
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def Good (m lambda k Qv : ℕ) (prefixes : Prefix k) : Prop :=
  0<prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize) ∧
    (∀ r,prefixes.read r≤prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)) ∧
    1+binaryWordWidth (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv

theorem native_good (m lambda k Qv : ℕ) (values : Summary k) (hPositive : 0<∑ r,values.read r)
    (hValues : ∀ r,values.read r≤4*(GeneralPaperPowerPrecision.prepare lambda k).unit) :
    Good m lambda k Qv (GeneralPaperEpochPrefixArray.build values) := by
  refine ⟨?_,GeneralPaperEpochPrefixQuery.read_le_total values,?_⟩
  · rw [GeneralPaperEpochPrefixQuery.read_total]
    exact hPositive
  · rw [GeneralPaperEpochPrefixArray.read_total]
    have hs := GeneralPaperEpochPrefixPrice.array_sum_bound values _ hValues
    exact (Nat.add_le_add_left (binaryWordWidth_mono hs) 1).trans
      (GeneralPaperEpochNumeratorEnvelope.total_word m lambda k Qv)

theorem block_good (m lambda k Qv : ℕ) (block : GeneralPaperEpochSnapshot.Block k)
    (hPositive : block.Positive) (hCoherent : block.Coherent)
    (hValues : ∀ r,block.values.read r≤4*(GeneralPaperPowerPrecision.prepare lambda k).unit) :
    Good m lambda k Qv block.cdf := by
  rw [hCoherent]
  exact native_good m lambda k Qv block.values hPositive hValues

theorem prefix_word (m lambda k Qv : ℕ) (prefixes : Prefix k) (hGood : Good m lambda k Qv prefixes)
    (r : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) :
    1+binaryWordWidth (prefixes.read r)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv :=
  (Nat.add_le_add_left (binaryWordWidth_mono (hGood.2.1 r)) 1).trans hGood.2.2

theorem difference_work (price : ℕ → ℕ) (hMono : Monotone price) (m lambda k Qv : ℕ)
    (prefixes : Prefix k) (hGood : Good m lambda k Qv prefixes)
    (lo hi : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) (prefixes.read hi) (prefixes.read lo)≤
      2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  exact (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a-b) _ _
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))
    (hGood.2.1 hi) (hGood.2.1 lo) ((Nat.sub_le _ _).trans (hGood.2.1 hi))).trans
      (Nat.mul_le_mul_left 2 (hMono hGood.2.2))

end Blotto.GeneralPaperMeshPrefixInvariant
