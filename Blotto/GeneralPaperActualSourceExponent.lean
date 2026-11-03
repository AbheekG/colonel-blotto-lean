import Blotto.GeneralPaperStoredExponentEnvelope

/-! Instantiate stored-exponent bounds with the actual source forests at
every reached epoch, and with every actual summary descent. The returned
preparation cache also supplies the identical native power/precision data.
-/
namespace Blotto.GeneralPaperActualSourceExponent
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem epoch_cached {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch : ℕ) (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    (mass (GeneralPaperPreparedPowers.prepare a.lambda k) (node learner trees j)).exponent.natAbs≤
      GeneralPaperQuantileExponentRange.cap a.lambda k := by
  exact GeneralPaperTreeMassRange.cached a.lambda k _ (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner j)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner j)

theorem epoch_fresh {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch : ℕ) (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    (fresh (GeneralPaperPreparedPowers.prepare a.lambda k) 0 (node learner trees j)).number.exponent.natAbs≤
      GeneralPaperQuantileExponentRange.cap a.lambda k := by
  exact GeneralPaperTreeMassRange.fresh a.lambda k 0 _ (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner j)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner j)

theorem epoch_descent {m : ℕ} (a : Alphabet) (k Qv width target size : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch : ℕ) (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let n := node learner trees j
    let total := (fresh (GeneralPaperPreparedPowers.prepare a.lambda k) 0 n).number
    GeneralPaperQuantileExponentRange.Safe a.lambda k width target size total
      (treeHeight learner a.lambda) n 0 total GeneralPaperDyadicFloat.zero := by
  exact GeneralPaperQuantileExponentRange.initial a.lambda k width target size _ _ (tree_height_bound learner a.lambda)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he learner j)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he learner j)

theorem prepared_epoch_descent {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (learner : Learner) (j : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := treesAt ready.1.2 a k epoch
    let n := node learner trees j
    let total := (fresh ready.2.source.powers 0 n).number
    GeneralPaperQuantileExponentRange.Safe a.lambda k ready.1.2.wordWidth (r.val+1)
      ready.2.source.controls.source.summarySize total (treeHeight learner a.lambda) n 0 total GeneralPaperDyadicFloat.zero := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_descent (GeneralPaperProxyParameters.alphabet m k) k Qv _ _ _ weights Bc Br epoch he learner j

theorem fresh_product_width (m lambda k Qv ancestor : ℕ) {height : ℕ} (n : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k n)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n) :
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    GeneralPaperDyadicMultiplyPrice.width prepared.format.unit prepared.format.fractionalBits
      (GeneralPaperPreparedPowers.query prepared (ancestor+offset n)).number (mass prepared n)≤
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hRoot : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 n := by
    intro i hi
    have hp := hPath i hi
    omega
  have hMass := GeneralPaperTreeMassRange.cached lambda k n hHeight hValid hRoot
  have hQuery := (GeneralPaperPowerQueryExponent.magnitude lambda k (ancestor+offset n)).trans
    (Nat.add_le_add_right (path_offset _ ancestor n hPath) _)
  have hQueryCap : (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k)
      (ancestor+offset n)).number.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k := by
    unfold GeneralPaperQuantileExponentRange.cap
    omega
  exact GeneralPaperStoredExponentEnvelope.multiply_width m lambda k Qv _ _ hQueryCap hMass

end Blotto.GeneralPaperActualSourceExponent
