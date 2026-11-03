import Blotto.GeneralPaperCatalogueFiniteCDF
import Blotto.GeneralPaperCatalogueGlobalOptimizer

/-! Reindex actual unsigned and signed geometric laws to the common
finite game alphabets I and (+I,-I). Reindexing preserves probabilities,
prefix CDFs and regret pairings; it never enumerates either alphabet at
runtime. Both sign halves remain one normalized probability distribution.
-/
namespace Blotto.GeneralPaperCatalogueFiniteFamilies
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOccurrenceHistory GeneralPaperCodeCDF GeneralPaperCatalogueFiniteCDF
set_option autoImplicit false
set_option maxHeartbeats 3500000

def resize {n p : ℕ} (h : n=p) (f : Fin n → ℝ) (i : Fin p) : ℝ := f ⟨i.val,by rw [h]; exact i.isLt⟩

theorem resize_probability {n p : ℕ} (h : n=p) (f : Fin n → ℝ) (hf : Probability f) : Probability (resize h f) := by
  cases h
  exact hf

theorem resize_prefix {n p : ℕ} (h : n=p) (f : Fin n → ℝ) (cut : ℕ) : prefixSum (resize h f) cut=prefixSum f cut := by
  cases h
  rfl

theorem resize_dot {n p : ℕ} (h : n=p) (f g : Fin n → ℝ) :
    GeneralPaperFourLossAlgebra.dot (resize h f) (resize h g)=GeneralPaperFourLossAlgebra.dot f g := by
  cases h
  rfl

theorem unsigned_size (response : Bool) (a : Alphabet) :
    2^(treeHeight (GeneralPaperCatalogueExecutedErrors.unsignedLearner response) a.lambda)=2^a.lambda := by
  cases response <;> rfl

theorem signed_size (response : Bool) (a : Alphabet) :
    2^(treeHeight (GeneralPaperCatalogueTrueScore.signedLearner response) a.lambda)=2^a.lambda+2^a.lambda := by
  cases response <;> simp only [GeneralPaperCatalogueTrueScore.signedLearner,Bool.false_eq_true,ite_false,ite_true,treeHeight,pow_succ] <;> omega

noncomputable def unsigned {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Fin (2^a.lambda) → ℝ :=
  resize (unsigned_size response a) (family (GeneralPaperCatalogueExecutedErrors.unsignedLearner response) a k Qv weights Bc Br time j)

noncomputable def signedFamily {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Fin (2^a.lambda+2^a.lambda) → ℝ :=
  resize (signed_size response a) (family (GeneralPaperCatalogueTrueScore.signedLearner response) a k Qv weights Bc Br time j)

theorem unsigned_probability {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Probability (unsigned response a k Qv weights Bc Br time j) :=
  resize_probability _ _ (family_probability _ a k Qv weights Bc Br time j)

theorem signed_probability {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Probability (signedFamily response a k Qv weights Bc Br time j) :=
  resize_probability _ _ (family_probability _ a k Qv weights Bc Br time j)

theorem unsigned_prefix {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (cut : ℕ) (hc : cut≤2^a.lambda) :
    prefixSum (unsigned response a k Qv weights Bc Br time j) cut=
      GeneralPaperCatalogueExecutedErrors.cdf (GeneralPaperCatalogueExecutedErrors.unsignedLearner response)
        (GeneralPaperCatalogueOuterLoop.cacheAt (prepare a k Qv weights Bc Br) a k
          (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)) Qv weights Bc Br
        (GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br _
          (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le)
        (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j cut := by
  rw [unsigned,resize_prefix]
  exact exact_time_prefix _ a k Qv weights Bc Br time ht j cut (by rw [unsigned_size]; exact hc)

theorem signed_prefix {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (cut : ℕ) (hc : cut≤2^a.lambda+2^a.lambda) :
    prefixSum (signedFamily response a k Qv weights Bc Br time j) cut=
      GeneralPaperCatalogueExecutedErrors.cdf (GeneralPaperCatalogueTrueScore.signedLearner response)
        (GeneralPaperCatalogueOuterLoop.cacheAt (prepare a k Qv weights Bc Br) a k
          (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)) Qv weights Bc Br
        (GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br _
          (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le)
        (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j cut := by
  rw [signedFamily,resize_prefix]
  exact exact_time_prefix _ a k Qv weights Bc Br time ht j cut (by rw [signed_size]; exact hc)

def row {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Fin (2^a.lambda) :=
  ⟨(GeneralPaperCatalogueGlobalOptimizer.chosen response a k Qv weights Bc Br time).read j,by
    have h := GeneralPaperCatalogueTrueScore.chosen_bound response
      (GeneralPaperCatalogueEpochRun.selected
        (GeneralPaperCatalogueOuterLoop.cacheAt (prepare a k Qv weights Bc Br) a k
          (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)) Qv weights Bc Br)
      (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j
    rw [← a.dyadic]
    exact h⟩

end Blotto.GeneralPaperCatalogueFiniteFamilies
