import Blotto.GeneralPaperCataloguePairingRegret

/-! The actual native optimizer guarantees are inequalities for the exact
finite signed-CDF pairing used in four-loss cancellation. Both comparators
and returned choices use the same literal code rows and symbolic budgets.
No independently supplied optimization certificate is assumed.
-/
namespace Blotto.GeneralPaperCatalogueFiniteOptimizer
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeCDF GeneralPaperSignedPairing
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueFiniteFamilies GeneralPaperCatalogueFiniteLosses
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem score_tail {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (codes : FixedArrayTable m ℕ)
    (hc : ∀ j, codes.read j<2^a.lambda) :
    GeneralPaperCatalogueGlobalOptimizer.score response a k Qv weights Bc Br time ht codes=
      ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*tail (signedFamily response a k Qv weights Bc Br time j) (codes.read j) := by
  unfold GeneralPaperCatalogueGlobalOptimizer.score GeneralPaperCatalogueTrueScore.trueScore
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun value => (weights.read j:ℝ)/Qv*value)
  have he := tail_components response a k Qv weights Bc Br time ht j (⟨codes.read j,hc j⟩:Fin (2^a.lambda))
  unfold GeneralPaperCatalogueQueryErrors.signedTail
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  have hu : 8*c.alphabet.C=2^a.lambda := a.dyadic
  rw [hu,two_mul]
  exact he.symm

theorem chosen_bound {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : (GeneralPaperCatalogueGlobalOptimizer.chosen response a k Qv weights Bc Br time).read j<2^a.lambda :=
  (row response a k Qv weights Bc Br time j).isLt

theorem decoded_bound {m : ℕ} (response : Bool) (a : Alphabet) (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hd : ∀ j, (GeneralPaperCodeDecode.decode a response (codes.read j)).choice=some (choices.read j)) (j : Fin m) :
    codes.read j<2^a.lambda := by
  rw [← a.dyadic]
  exact valid_in_alphabet a response (codes.read j) (GeneralPaperCodeDecodeSound.decode_valid a response _ _ (hd j))

theorem optimizer_residual {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (time : ℕ)
    (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (codes : FixedArrayTable m ℕ)
    (choices : FixedArrayTable m Choice) (hDecode : ∀ j, (GeneralPaperCodeDecode.decode a response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤GeneralPaperResponseTag.budget (if response then Br else Bc)) :
    -(25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16)≤
      ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
        (tail (signedFamily response a k Qv weights Bc Br time j) (row response a k Qv weights Bc Br time j).val-
          tail (signedFamily response a k Qv weights Bc Br time j) (codes.read j)) := by
  have ho := GeneralPaperCatalogueGlobalOptimizer.optimality response a k Qv hQv weights hWeights Bc Br time ht codes choices hDecode hBudget
  rw [score_tail response a k Qv weights Bc Br time ht codes (decoded_bound response a codes choices hDecode),
    score_tail response a k Qv weights Bc Br time ht _ (chosen_bound response a k Qv weights Bc Br time)] at ho
  have he : (∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
      (tail (signedFamily response a k Qv weights Bc Br time j) (row response a k Qv weights Bc Br time j).val-
        tail (signedFamily response a k Qv weights Bc Br time j) (codes.read j)))=
    (∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
      tail (signedFamily response a k Qv weights Bc Br time j) ((GeneralPaperCatalogueGlobalOptimizer.chosen response a k Qv weights Bc Br time).read j))-
    ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*tail (signedFamily response a k Qv weights Bc Br time j) (codes.read j) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    rfl
  rw [he]
  linarith only [ho]

end Blotto.GeneralPaperCatalogueFiniteOptimizer
