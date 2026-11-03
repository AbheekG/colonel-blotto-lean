import Blotto.GeneralPaperChildMassStatePrice

/-! Fresh queries on actual retained epoch states. Forest expressions
identify already-produced states, not extra calls charged to this operation.
The returned preparation cache discharges all parameter and state premises.
-/
namespace Blotto.GeneralPaperActualFreshMassPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem epoch_data {m : ℕ} (primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) j
    (GeneralPaperFreshMassPrice.run primitive W c 0 n).1=fresh c.powers 0 n := by
  exact GeneralPaperFreshMassPrice.data primitive W m a.lambda k Qv c hc 0 _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner j)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner j)

theorem epoch_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) j
    (GeneralPaperFreshMassPrice.run primitive W c 0 n).2≤
      524288*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)*
        (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv)) := by
  exact GeneralPaperFreshMassPrice.work primitive hMono W m a.lambda k Qv c hc 0 _ (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner j)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner j)

theorem epoch_certificate {m : ℕ} (primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) j
    Bound (GeneralPaperPreparedPowers.prepare a.lambda k).format.unit (queryExponent a.lambda k) (trueMass k 0 n)
      (GeneralPaperFreshMassPrice.run primitive W c 0 n).1.number := by
  dsimp only
  rw [epoch_data primitive W k Qv a c hc weights Bc Br epoch he learner j,hc]
  exact fresh_bound a.lambda k 0 _ (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner j)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner j)

theorem epoch_arithmetic_work {m : ℕ} (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (learner : Learner) (j : Fin m) :
    let n := node learner (treesAt (prepare a k Qv weights Bc Br) a k epoch) j
    (GeneralPaperFreshMassPrice.arithmetic c 0 n).2≤1048576*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)^2 :=
  GeneralPaperFreshMassPrice.arithmetic_work m a.lambda k Qv c hc 0 _

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (learner : Learner) (j : Fin m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let n := node learner (treesAt ready.1.2 a k epoch) j
    (GeneralPaperFreshMassPrice.run model.rat W ready.2.source 0 n).2≤
      524288*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)*
        (W+model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv)) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model.rat model.monotone W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl
    weights Bc Br epoch he learner j

theorem prepared_epoch_same_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (learner : Learner) (j : Fin m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let n := node learner (treesAt ready.1.2 a k epoch) j
    (GeneralPaperFreshMassPrice.run model.rat W ready.2.source 0 n).1=(GeneralPaperFreshMassPrice.arithmetic ready.2.source 0 n).1 := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  apply GeneralPaperFreshMassPrice.same_data model.rat W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ rfl
  · exact GeneralPaperCatalogueOuterValidity.trees_valid _ _ _ _ _ _ epoch he learner j
  · exact GeneralPaperCatalogueOuterValidity.trees_paths _ _ _ _ _ _ epoch he learner j

end Blotto.GeneralPaperActualFreshMassPrice
