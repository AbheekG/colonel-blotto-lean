import Blotto.GeneralPaperArithmeticSourcePairDriver

/-! Computable rational-input source/compiler pair. The rational streaming
front end and retained materialization return the same exact physical pair
as the arithmetic front end. This closes data correctness, not the complete
bit ledger: the work total still combines front-end bit prices with the
downstream arithmetic counters. Wf/Wg capacities remain explicit. -/
namespace Blotto.GeneralPaperRationalSourcePairData
open GeneralPaperProxyParameters GeneralPaperCachedSourcePair GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem input_unique {m k Qv : ℕ} {b : ℝ} (x y : Input m k Qv b) : x=y := by
  obtain ⟨xc,xa,xg,xf,hxc,hxa,hxg,hxf⟩ := x
  obtain ⟨yc,ya,yg,yf,hyc,hya,hyg,hyf⟩ := y
  subst xc;subst xa;subst xg;subst xf
  subst yc;subst ya;subst yg;subst yf
  rfl

def prepare (model : RationalCostModel) (Wf Wg m k Qv : ℕ) (b : ℚ) : Input m k Qv (b:ℝ)×ℕ :=
  let front := GeneralPaperSourcePrecallPreparation.prepare model Wf m k Qv b
  let grid := GeneralPaperMaterializationFromControls.bit model Wg k front.1.2
  let hFront := GeneralPaperSourcePrecallPreparation.data model Wf m k Qv b
  let hA : front.1.1.1.2=alphabet m k := congrArg (fun r => r.1.1.2) hFront
  let hControls : front.1.2=GeneralPaperSourcePreparationCache.specification m front.1.1.1.2.lambda k Qv := by
    rw [hA]
    exact congrArg Prod.snd hFront
  let hGrid := GeneralPaperMaterializationFromControls.bit_data model Wg m front.1.1.1.2.lambda k Qv front.1.2 hControls
  (⟨front.1.1.1.1,front.1.1.1.2,grid.1,front.1.1.2,
    congrArg (fun r => r.1.1.1) hFront,hA,hGrid,congrArg (fun r => r.1.2) hFront⟩,
    front.2+grid.2+128)

def run {m : ℕ} (model : RationalCostModel) (Wf Wg k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv) (b : ℚ) :
    Option (Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (GeneralPaperProxyParameters.prepare m k).K)×ℕ :=
  let prepared := prepare model Wf Wg m k Qv b
  let result := GeneralPaperCachedSourcePair.run model k Qv hQv weights hp hw (b:ℝ) prepared.1
  (result.1,prepared.2+result.2+64)

theorem arithmetic_data {m : ℕ} (model : RationalCostModel) (Wf Wg k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv) (b : ℚ) :
    (run model Wf Wg k Qv hQv weights hp hw b).1=
      (GeneralPaperArithmeticSourcePairDriver.run model k Qv hQv weights hp hw (b:ℝ)).1 := by
  dsimp only [run,GeneralPaperArithmeticSourcePairDriver.run]
  exact congrArg (fun x : Input m k Qv (b:ℝ) =>
    (GeneralPaperCachedSourcePair.run model k Qv hQv weights hp hw (b:ℝ) x).1)
    (input_unique (prepare model Wf Wg m k Qv b).1 (GeneralPaperArithmeticPairPreparation.run m k Qv (b:ℝ)).1)

theorem data {m : ℕ} (model : RationalCostModel) (Wf Wg k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    (run model Wf Wg k Qv hQv weights hp hw b).1.map GeneralPaperPhysicalColumnPair.decode=
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hw (b:ℝ) := by
  rw [arithmetic_data]
  exact GeneralPaperArithmeticSourcePairDriver.data model k Qv hm hQv weights hp hw (b:ℝ) (by exact_mod_cast hb)

theorem actual_return {m : ℕ} (model : RationalCostModel) (Wf Wg k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(run model Wf Wg k Qv hQv weights hp hw b).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hw (b:ℝ)=some pair ∧ Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hw (b:ℝ) pair := by
  obtain ⟨physical,pair,hRun,hPair,hMatch,hContract⟩ := GeneralPaperArithmeticSourcePairDriver.actual_return model k Qv hm hQv
    weights hp hw (b:ℝ) (by exact_mod_cast hb)
  exact ⟨physical,pair,(arithmetic_data model Wf Wg k Qv hQv weights hp hw b).trans hRun,hPair,hMatch,hContract⟩

end Blotto.GeneralPaperRationalSourcePairData
