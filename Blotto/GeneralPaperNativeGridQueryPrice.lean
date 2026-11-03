import Blotto.GeneralPaperCachedProfitGridPrice
import Blotto.GeneralPaperActualNativeProfitFields

/-! Actual option fields discharge the profit-grid query cap from cached
tail counts and rounded weights. These are observer proofs only. Neither
the native input nor its query is reconstructed to measure its operands. -/
namespace Blotto.GeneralPaperNativeGridQueryPrice
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem numerator_bound {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R] {K k : ℕ}
    (m lambda Qv T weight : ℕ) (prefixes : Prefix k) (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K)
    (i : Fin K) (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeight : weight≤Qv)
    (hMesh : plan.mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hGood : GeneralPaperMeshPrefixInvariant.Good m lambda k Qv prefixes) :
    ((GeneralPaperOrderedNativeOptionProfits.build k T weight prefixes plan).1.read i).1≤
      2*(GeneralPaperProfitParameters.parameters m lambda k Qv).qProf := by
  have hp := GeneralPaperMeshCountBounds.cached_interval_bound true (fun _ => 1) 1 m lambda Qv plan.mesh prefixes
    plan.tails.positive i.castSucc (Fin.last K) hMesh hGood
  change (GeneralPaperMeshPairExecution.tails true (fun _ => 1) 1 plan.mesh prefixes plan.tails i).1.positive≤plan.mesh at hp
  rw [GeneralPaperMeshPairExecution.tails_data true (fun _ => 1) 1 plan.mesh _ _ _ hMesh,hMesh] at hp
  rw [GeneralPaperOrderedNativeOptionProfits.read_build,hT,hMesh]
  exact GeneralPaperCachedProfitGridPrice.native_profit_bound m lambda k Qv weight _ _ hWeight hp

theorem leaf_work {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R] {K k : ℕ}
    (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda Qv T weight : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hPrepared : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (prefixes : Prefix k) (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) (i : Fin K)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeight : weight≤Qv)
    (hMesh : plan.mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hGood : GeneralPaperMeshPrefixInvariant.Good m lambda k Qv prefixes) :
    (GeneralPaperProfitGridRoundExecution.leaf true primitive W prepared.grid
      ((GeneralPaperOrderedNativeOptionProfits.build k T weight prefixes plan).1.read i).1).2≤
        GeneralPaperCachedProfitGridPrice.profile primitive W m lambda k Qv := by
  subst prepared
  exact GeneralPaperCachedProfitGridPrice.leaf_work primitive hMono W m lambda k Qv _ rfl _ rfl _
    (numerator_bound m lambda Qv T weight prefixes plan i hT hWeight hMesh hGood)

theorem ready_leaf_work {m k : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W lambda Qv T : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hPrepared : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeights : ∑ a,weights.read a=Qv)
    (hGood : GeneralPaperMeshPrefixInvariant.Good m lambda k Qv (prefixes.read j)) :
    (GeneralPaperProfitGridRoundExecution.leaf true primitive W prepared.grid
      ((GeneralPaperOrderedNativeOptionProfits.build k T (weights.read j) (prefixes.read j) (ready.cached.read j)).1.read i).1).2≤
        GeneralPaperCachedProfitGridPrice.profile primitive W m lambda k Qv :=
  leaf_work primitive hMono W m lambda Qv T (weights.read j) prepared hPrepared (prefixes.read j) (ready.cached.read j) i
    hT (GeneralPaperNativeProfitFieldsPrice.weight_bound weights Qv hWeights j)
    (GeneralPaperActualNativeProfitFields.meshes ready j) hGood

end Blotto.GeneralPaperNativeGridQueryPrice
