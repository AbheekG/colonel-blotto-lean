import Blotto.RationalRejectionOutputLaw

/-! Native true-label output uses the stored rational record index, with the
real view's size equality erased as proof. It equals the semantic trueOutput;
the final fallback law is therefore a theorem for executable output too. -/

namespace Blotto
namespace RationalWeightedGuideTree

def nativeTrueOutput (tree : RationalWeightedGuideTree) (record : tree.Record) : Fin tree.trueSize := tree.output record

theorem nativeTrueOutput_eq (tree : RationalWeightedGuideTree) (record : tree.Record) :
    (tree.nativeTrueOutput record).cast tree.real_trueSize.symm = tree.trueOutput record := by
  induction tree with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    rcases record with ⟨i, r, l⟩
    apply Fin.ext
    change (finProdFinEquiv (left.output l, right.output r)).val =
      (finProdFinEquiv (left.real.proposalOutput (left.recordReal l), right.real.proposalOutput (right.recordReal r))).val
    have hL := congrArg Fin.val (ihL l)
    have hR := congrArg Fin.val (ihR r)
    have hSize := right.real_trueSize
    simp only [finProdFinEquiv_apply_val]
    unfold nativeTrueOutput trueOutput at hL hR
    simp only [Fin.val_cast] at hL hR
    rw [hL, hR]
    exact congrArg (fun size : ℕ => (right.real.proposalOutput (right.recordReal r)).val +
      size * (left.real.proposalOutput (left.recordReal l)).val) hSize.symm

def rejectionNativeOutput (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.trueSize) (bits : Fin (attempts * tree.attemptBitBudget K) → Bool) : Fin tree.trueSize :=
  ((tree.rejectionFinite hc B hm K attempts bits).map tree.nativeTrueOutput).getD fallback

theorem rejectionNativeOutput_eq (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.trueSize) (bits : Fin (attempts * tree.attemptBitBudget K) → Bool) :
    (tree.rejectionNativeOutput hc B hm K attempts fallback bits).cast tree.real_trueSize.symm =
      tree.rejectionOutput hc B hm K attempts (fallback.cast tree.real_trueSize.symm) bits := by
  unfold rejectionNativeOutput rejectionOutput
  cases he : tree.rejectionFinite hc B hm K attempts bits with
  | none => rfl
  | some record => exact tree.nativeTrueOutput_eq record

end RationalWeightedGuideTree
end Blotto
