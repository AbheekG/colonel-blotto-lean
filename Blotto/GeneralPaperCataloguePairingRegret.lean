import Blotto.GeneralPaperCatalogueFourPairings

/-! The four actual finite-code pairings sum to the previously proved
global regret of this execution. Alphabet reindexing changes neither a
comparator's probability nor a loss pairing. No independently supplied
loss sequence, convergence certificate or row history enters the bound.
-/
namespace Blotto.GeneralPaperCataloguePairingRegret
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeCDF GeneralPaperCatalogueFiniteFamilies
open GeneralPaperCatalogueFiniteLosses GeneralPaperFourLossAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

def comparator (a : Alphabet) (x y : Fin (2^a.lambda) → ℝ)
    (testLambda testMu : Fin (2^a.lambda+2^a.lambda) → ℝ) :
    (block : Fin 4) → Fin (GeneralPaperCatalogueGlobalRegret.size a block) → ℝ
  | ⟨0,_⟩ => x
  | ⟨1,_⟩ => y
  | ⟨2,_⟩ => resize (signed_size false a).symm testLambda
  | ⟨3,_⟩ => resize (signed_size true a).symm testMu
  | ⟨b+4,h⟩ => False.elim (by omega)

theorem comparator_probability (a : Alphabet) (x y : Fin (2^a.lambda) → ℝ)
    (testLambda testMu : Fin (2^a.lambda+2^a.lambda) → ℝ)
    (hx : Probability x) (hy : Probability y) (hl : Probability testLambda) (hm : Probability testMu) (block : Fin 4) :
    Probability (comparator a x y testLambda testMu block) := by
  fin_cases block
  · exact hx
  · exact hy
  · exact resize_probability (signed_size false a).symm testLambda hl
  · exact resize_probability (signed_size true a).symm testMu hm

theorem step_sum {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (x y : Fin (2^a.lambda) → ℝ) (testLambda testMu : Fin (2^a.lambda+2^a.lambda) → ℝ) :
    (∑ block : Fin 4, dot
      (fun i => GeneralPaperCatalogueFiniteCDF.family (GeneralPaperCatalogueGlobalRegret.learner block) a k Qv weights Bc Br time j i-
        comparator a x y testLambda testMu block i)
      (fun i => GeneralPaperCatalogueGlobalErrors.truth (GeneralPaperCatalogueGlobalRegret.learner block) a k Qv weights Bc Br time j i))=
      GeneralPaperCatalogueFourPairings.pairings a k Qv weights Bc Br time j x y testLambda testMu := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  unfold GeneralPaperCatalogueFourPairings.pairings unsigned signedFamily unsignedTruth signedTruth
  rw [GeneralPaperCatalogueFourPairings.resize_regret,GeneralPaperCatalogueFourPairings.resize_regret,
    GeneralPaperCatalogueFourPairings.resize_regret,GeneralPaperCatalogueFourPairings.resize_regret]
  simp only [add_assoc]
  rfl

theorem average_identity {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (x y : Fin m → Fin (2^a.lambda) → ℝ)
    (testLambda testMu : Fin m → Fin (2^a.lambda+2^a.lambda) → ℝ) :
    GeneralPaperCatalogueGlobalRegret.averageRegret a k Qv weights Bc Br
      (fun block j => comparator a (x j) (y j) (testLambda j) (testMu j) block)=
      (∑ time ∈ Finset.range (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows,
        ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
          GeneralPaperCatalogueFourPairings.pairings a k Qv weights Bc Br time j (x j) (y j) (testLambda j) (testMu j))/
            (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows := by
  unfold GeneralPaperCatalogueGlobalRegret.averageRegret GeneralPaperFourBlockRegret.weightedRegret GeneralPaperGeometricRegret.cumulative
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro time ht
  simp_rw [← Finset.mul_sum]
  exact congrArg (fun value => GeneralPaperCatalogueGlobalRegret.values Qv weights j*value)
    (step_sum a k Qv weights Bc Br time j (x j) (y j) (testLambda j) (testMu j))

theorem average_bound {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (x y : Fin m → Fin (2^a.lambda) → ℝ)
    (testLambda testMu : Fin m → Fin (2^a.lambda+2^a.lambda) → ℝ)
    (hx : ∀ j, Probability (x j)) (hy : ∀ j, Probability (y j))
    (hl : ∀ j, Probability (testLambda j)) (hm : ∀ j, Probability (testMu j)) :
    (∑ time ∈ Finset.range (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows,
      ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
        GeneralPaperCatalogueFourPairings.pairings a k Qv weights Bc Br time j (x j) (y j) (testLambda j) (testMu j))/
          (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows+
      2*(25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16)<((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  rw [← average_identity]
  apply GeneralPaperCatalogueGlobalRegret.regret_with_optimizer_slack a k Qv hQv weights hWeights Bc Br
    (fun block j => comparator a (x j) (y j) (testLambda j) (testMu j) block)
  · intro block j i
    exact (comparator_probability a (x j) (y j) (testLambda j) (testMu j) (hx j) (hy j) (hl j) (hm j) block).1 i
  · intro block j
    exact (comparator_probability a (x j) (y j) (testLambda j) (testMu j) (hx j) (hy j) (hl j) (hm j) block).2

end Blotto.GeneralPaperCataloguePairingRegret
