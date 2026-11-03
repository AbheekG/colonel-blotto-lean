import Blotto.GeneralPaperCachedSourcePair

/-! Literal returned-pair correctness for every actual retained cache.
The postcondition derives Matches from both returned source/column arrays;
it is not a supplied security or dictionary premise. -/
namespace Blotto.GeneralPaperCachedSourcePairLaw
open GeneralPaperCachedSourcePair GeneralPaperProxyParameters GeneralPaperCatalogueShared
open GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (x : Input m k Qv b) :
    (run model k Qv hQv weights hp hw b x).1.map GeneralPaperPhysicalColumnPair.decode=
      GeneralPaperCheckedSourcePair.run k Qv hQv weights hp hw b := by
  obtain ⟨control,a,grid,classified,hControl,hA,hGrid,hClass⟩ := x
  subst control
  subst a
  subst grid
  subst classified
  let g := GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv
  let rho := (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
  let rich := (GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k (alphabet m k) g weights 1 rho).1
  let poor := (GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k (alphabet m k) g weights rho 1).1
  have hr : rich=prepare (alphabet m k) k Qv weights 1 rho :=
    GeneralPaperCachedSharedPreparation.data (fun _ => 1) 1 k Qv (alphabet m k) g rfl weights 1 rho
  have hp' : poor=prepare (alphabet m k) k Qv weights rho 1 :=
    GeneralPaperCachedSharedPreparation.data (fun _ => 1) 1 k Qv (alphabet m k) g rfl weights rho 1
  have hRT : rich.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hr];rfl
  have hPT : poor.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows := by rw [hp'];rfl
  have hd := GeneralPaperPreparedSourceCompilerPair.data model k Qv hm hQv weights hp hw b hb g.source rfl rich poor hr hp' hRT hPT
  dsimp only [run]
  erw [GeneralPaperColumnPairReindex.map_reflexive]
  exact hd

theorem actual_return {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (x : Input m k Qv b) :
    ∃ physical pair,(run model k Qv hQv weights hp hw b x).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hw b=some pair ∧ Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hw b pair := by
  obtain ⟨pair,hPair,hContract⟩ := GeneralPaperCheckedSourcePair.run_contract k Qv hm hQv weights hp hw b hb
  have hd := data model k Qv hm hQv weights hp hw b hb x
  erw [hPair] at hd
  obtain ⟨physical,hRun,hDecode⟩ := Option.map_eq_some_iff.mp hd
  refine ⟨physical,pair,hRun,?_,(GeneralPaperPhysicalColumnPair.matches_iff physical pair).mpr hDecode,hContract⟩
  exact (GeneralPaperCheckedSourcePair.run_eq k Qv hm hQv weights hp hw b hb).symm.trans hPair

end Blotto.GeneralPaperCachedSourcePairLaw
