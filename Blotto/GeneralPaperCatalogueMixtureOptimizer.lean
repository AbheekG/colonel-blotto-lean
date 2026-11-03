import Blotto.GeneralPaperCodeMixture

/-! Extend the actual native optimizer inequality to arbitrary finite
whole-row feasible comparator laws, with real weights allowed. The source
does not construct or enumerate these proof comparators.
-/
namespace Blotto.GeneralPaperCatalogueMixtureOptimizer
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeMixture GeneralPaperCatalogueFiniteFamilies
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Feasible {m : ℕ} (a : Alphabet) (response : Bool) (B : ℚ) where
  law : Mixture m (2^a.lambda)
  choices : Fin law.labels → FixedArrayTable m Choice
  decoded : ∀ l j, (GeneralPaperCodeDecode.decode a response (law.rows l j).val).choice=some ((choices l).read j)
  budget : ∀ l, (∑ j, ((choices l).read j).tag)≤GeneralPaperResponseTag.budget B

def codes {m : ℕ} {a : Alphabet} {response : Bool} {B : ℚ} (law : Feasible (m:=m) a response B)
    (l : Fin law.law.labels) : FixedArrayTable m ℕ := FixedArrayTable.ofFn (fun j => (law.law.rows l j).val)

theorem codes_read {m : ℕ} {a : Alphabet} {response : Bool} {B : ℚ} (law : Feasible (m:=m) a response B)
    (l : Fin law.law.labels) (j : Fin m) : (codes law l).read j=(law.law.rows l j).val := FixedArrayTable.read_ofFn _ j

theorem residual_lower {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (time : ℕ)
    (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)
    (law : Feasible (m:=m) a response (if response then Br else Bc)) :
    -(25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16)≤
      ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
        (GeneralPaperSignedPairing.tail (signedFamily response a k Qv weights Bc Br time j) (row response a k Qv weights Bc Br time j).val-
          GeneralPaperSignedPairing.pair (signedFamily response a k Qv weights Bc Br time j) (GeneralPaperCodeCDF.cdf (GeneralPaperCodeMixture.marginal law.law j))) := by
  rw [weighted_residual law.law]
  have hrow (l : Fin law.law.labels) : -(25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16)≤
      ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
        (GeneralPaperSignedPairing.tail (signedFamily response a k Qv weights Bc Br time j) (row response a k Qv weights Bc Br time j).val-
          GeneralPaperSignedPairing.tail (signedFamily response a k Qv weights Bc Br time j) (law.law.rows l j).val) := by
    have he := GeneralPaperCatalogueFiniteOptimizer.optimizer_residual response a k Qv hQv weights hWeights Bc Br time ht
      (codes law l) (law.choices l) (by intro j; rw [codes_read]; exact law.decoded l j) (law.budget l)
    simpa only [codes_read] using he
  calc
    _ = ∑ l, law.law.weight l*(-(25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16)) := by
      rw [← Finset.sum_mul,law.law.total,one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hrow l) (law.law.nonnegative l))

end Blotto.GeneralPaperCatalogueMixtureOptimizer
