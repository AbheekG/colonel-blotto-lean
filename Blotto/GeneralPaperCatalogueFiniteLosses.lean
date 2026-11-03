import Blotto.GeneralPaperCatalogueFiniteFamilies

/-! The true losses of the executed code-history are exactly the finite
four-game derivatives. Prefix, signed-tail and chosen-row identities use
the same incoming forest and same native whole-row calls as the source.
-/
namespace Blotto.GeneralPaperCatalogueFiniteLosses
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCodeCDF GeneralPaperSignedPairing GeneralPaperCatalogueFiniteFamilies GeneralPaperFourLossAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

noncomputable def unsignedTruth {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Fin (2^a.lambda) → ℝ :=
  resize (unsigned_size response a) (fun i => GeneralPaperCatalogueGlobalErrors.truth
    (GeneralPaperCatalogueExecutedErrors.unsignedLearner response) a k Qv weights Bc Br time j i)

noncomputable def signedTruth {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Fin (2^a.lambda+2^a.lambda) → ℝ :=
  resize (signed_size response a) (fun i => GeneralPaperCatalogueGlobalErrors.truth
    (GeneralPaperCatalogueTrueScore.signedLearner response) a k Qv weights Bc Br time j i)

theorem tail_components {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (code : Fin (2^a.lambda)) :
    let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    let incoming := GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br _ (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le
    let F := fun cut => GeneralPaperCatalogueExecutedErrors.cdf (GeneralPaperCatalogueTrueScore.signedLearner response)
      c Qv weights Bc Br incoming (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j cut
    tail (signedFamily response a k Qv weights Bc Br time j) code.val=
      (F (2^a.lambda)-F code.val)-(F (2^a.lambda+2^a.lambda)-F (2^a.lambda+code.val)) := by
  dsimp only
  unfold tail
  rw [signed_prefix response a k Qv weights Bc Br time ht j (2^a.lambda) (Nat.le_add_right _ _),
    signed_prefix response a k Qv weights Bc Br time ht j code.val (code.isLt.le.trans (Nat.le_add_right _ _)),
    signed_prefix response a k Qv weights Bc Br time ht j (2^a.lambda+2^a.lambda) le_rfl,
    signed_prefix response a k Qv weights Bc Br time ht j (2^a.lambda+code.val) (Nat.add_le_add_left code.isLt.le _)]

theorem p_loss {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m) (code : Fin (2^a.lambda)) :
    unsignedTruth false a k Qv weights Bc Br time j code=
      pLoss (unsigned true a k Qv weights Bc Br time j) (signedFamily false a k Qv weights Bc Br time j) code := by
  change GeneralPaperCatalogueGlobalErrors.truth .p a k Qv weights Bc Br time j code=_
  rw [GeneralPaperCatalogueGlobalErrors.truth_actual .p a k Qv weights Bc Br time ht j code]
  change GeneralPaperCatalogueExecutedErrors.unsignedLoss false _ Qv weights Bc Br _ _ j code.val=_
  unfold GeneralPaperCatalogueExecutedErrors.unsignedLoss GeneralPaperNativeLossErrors.trueLoss pLoss half cdf
  rw [unsigned_prefix true a k Qv weights Bc Br time ht j _ code.isLt.le,
    unsigned_prefix true a k Qv weights Bc Br time ht j _ (by have := code.isLt; omega),
    tail_components false a k Qv weights Bc Br time ht j code]
  change _=(1-(_+_)/2)+((_ - _)-(_ - _))
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  have hu : 8*c.alphabet.C=2^a.lambda := a.dyadic
  rw [hu,two_mul]
  rfl

theorem q_loss {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m) (code : Fin (2^a.lambda)) :
    unsignedTruth true a k Qv weights Bc Br time j code=
      qLoss (unsigned false a k Qv weights Bc Br time j) (signedFamily true a k Qv weights Bc Br time j) code := by
  change GeneralPaperCatalogueGlobalErrors.truth .q a k Qv weights Bc Br time j code=_
  rw [GeneralPaperCatalogueGlobalErrors.truth_actual .q a k Qv weights Bc Br time ht j code]
  change GeneralPaperCatalogueExecutedErrors.unsignedLoss true _ Qv weights Bc Br _ _ j code.val=_
  unfold GeneralPaperCatalogueExecutedErrors.unsignedLoss GeneralPaperNativeLossErrors.trueLoss qLoss half cdf
  rw [unsigned_prefix false a k Qv weights Bc Br time ht j _ code.isLt.le,
    unsigned_prefix false a k Qv weights Bc Br time ht j _ (by have := code.isLt; omega),
    tail_components true a k Qv weights Bc Br time ht j code]
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  have hu : 8*c.alphabet.C=2^a.lambda := a.dyadic
  rw [hu]
  simp only [GeneralPaperCatalogueExecutedErrors.unsignedLearner,GeneralPaperCatalogueExecutedErrors.opponentLearner,GeneralPaperCatalogueTrueScore.signedLearner,ite_true,ite_false,zero_sub,neg_div,two_mul] <;> rfl

theorem signed_loss {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (s : Fin (2^a.lambda+2^a.lambda)) :
    signedTruth response a k Qv weights Bc Br time j s=
      multiplierLoss (unsigned response a k Qv weights Bc Br time j) (row response a k Qv weights Bc Br time j) s := by
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  let code : Fin (2^(GeneralPaperCatalogueTreeCache.treeHeight (GeneralPaperCatalogueTrueScore.signedLearner response) a.lambda)) :=
    ⟨s.val,by rw [signed_size]; exact s.isLt⟩
  change GeneralPaperCatalogueGlobalErrors.truth (GeneralPaperCatalogueTrueScore.signedLearner response) a k Qv weights Bc Br time j code=_
  rw [GeneralPaperCatalogueGlobalErrors.truth_actual _ a k Qv weights Bc Br time ht j code]
  have hexact : GeneralPaperCatalogueExecutedErrors.exactLoss (GeneralPaperCatalogueTrueScore.signedLearner response)
      c Qv weights Bc Br (GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br _
        (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le)
      (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j code.val=
    GeneralPaperCatalogueExecutedErrors.signedLoss response c Qv weights Bc Br
      (GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br _
        (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le)
      (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j s.val := by cases response <;> rfl
  rw [hexact]
  unfold GeneralPaperCatalogueExecutedErrors.signedLoss multiplierLoss signed rowCDF cdf
  dsimp only
  have hCDF := unsigned_prefix response a k Qv weights Bc Br time ht j ((project s).val+1) (by have := (project s).isLt; omega)
  rw [hCDF]
  have hu : 8*c.alphabet.C=2^a.lambda := a.dyadic
  rw [hu]
  have hp : GeneralPaperSignedUpdatePlan.project (2^a.lambda) s.val=(project s).val := by
    unfold GeneralPaperSignedUpdatePlan.project project
    split_ifs <;> rfl
  rw [hp]
  have hr : (GeneralPaperCatalogueTrueScore.chosenCodes response (GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br)
      (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)).read j=(row response a k Qv weights Bc Br time j).val := rfl
  rw [hr]
  simp only [decide_eq_true_eq]
  split_ifs <;> ring

end Blotto.GeneralPaperCatalogueFiniteLosses
