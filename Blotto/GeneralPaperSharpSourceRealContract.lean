import Blotto.GeneralPaperSharpSourceRealRate

/-! Sharp real-RAM and fast-bit prices apply to the same native source data.
The real-RAM logarithms use only constructed parameters. Original inputs and
budgets are preserved; the analysis-only height-removal map is not executed. -/
namespace Blotto.GeneralPaperSharpSourceRealContract
open GeneralPaperSourceWordGrowth GeneralPaperSourceCoreLogBound GeneralPaperSharpSourceRealRate
open GeneralPaperFastRationalModel GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def NativeTime (actual : RationalCostModel) (x : Input) (count bound : ℕ) : Prop :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m a.lambda x.k x.Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  (GeneralPaperGeometricSourceExecution.run false (fun _ => 1) actual 1 x.k x.Qv a c hc ready.1.2 count).2≤bound

theorem native_time (actual : RationalCostModel) (x : Input) (count bound : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
    (hp : GeneralPaperGeometricSourcePrice.arithmeticProfile x.m x.k x.Qv (alphabet x) count≤bound) :
    NativeTime actual x count bound := by
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  have ha : a=alphabet x := by dsimp only [a,ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  have hc : c=GeneralPaperMaterializedPowerCache.specification x.m a.lambda x.k x.Qv := by
    dsimp only [c,a,ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  have hs : ready.1.2=GeneralPaperCatalogueShared.prepare a x.k x.Qv x.weights Bc Br := by
    dsimp only [ready,a]; rw [GeneralPaperPreparedSharedSource.data]
  have he' : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda x.k).epochs := by rw [ha]; exact he
  have ht := (GeneralPaperGeometricSourcePrice.work actual 1 x.k x.Qv a c hc x.weights Bc Br x.weight_sum count he').2
  have hp' : GeneralPaperGeometricSourcePrice.arithmeticProfile x.m x.k x.Qv a count≤bound := by rw [ha]; exact hp
  change (GeneralPaperGeometricSourceExecution.run false (fun _ => 1) actual 1 x.k x.Qv a c hc ready.1.2 count).2≤bound
  rw [hs]
  exact ht.trans hp'

def OutputAgreement (actual : RationalCostModel) (x : Input) (count W : ℕ) : Prop :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m a.lambda x.k x.Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  (GeneralPaperGeometricSourceExecution.run false (fun _ => 1) actual 1 x.k x.Qv a c hc ready.1.2 count).1=
    (GeneralPaperGeometricSourceExecution.run true (fun w => w) actual W x.k x.Qv a c hc ready.1.2 count).1

theorem same_output (actual : RationalCostModel) (x : Input) (count W : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) :
    OutputAgreement actual x count W := by
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  have ha : a=alphabet x := by dsimp only [a,ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  have hc : c=GeneralPaperMaterializedPowerCache.specification x.m a.lambda x.k x.Qv := by
    dsimp only [c,a,ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  have hs : ready.1.2=GeneralPaperCatalogueShared.prepare a x.k x.Qv x.weights Bc Br := by
    dsimp only [ready,a]; rw [GeneralPaperPreparedSharedSource.data]
  have he' : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda x.k).epochs := by rw [ha]; exact he
  have hr := GeneralPaperGeometricSourceExecution.data false (fun _ => 1) actual 1 x.k x.Qv a c hc x.weights Bc Br count he'
  have hb := GeneralPaperGeometricSourceExecution.data true (fun w => w) actual W x.k x.Qv a c hc x.weights Bc Br count he'
  change (GeneralPaperGeometricSourceExecution.run false (fun _ => 1) actual 1 x.k x.Qv a c hc ready.1.2 count).1=
    (GeneralPaperGeometricSourceExecution.run true (fun w => w) actual W x.k x.Qv a c hc ready.1.2 count).1
  rw [hs]
  exact hr.trans hb.symm

theorem prefix_time_bound (actual : RationalCostModel) : ∃ A e : ℕ,∀ (x : Input) (count : ℕ),
    count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
    NativeTime actual x count (A*sourceRate x*(coreLog x)^e) := by
  rcases prefix_profile_bound with ⟨A,e,hA⟩
  exact ⟨A,e,fun x count he => native_time actual x count _ he (hA x count he)⟩

theorem paper_time_bound (actual : RationalCostModel) : ∃ A e : ℕ,∀ (x : Input) (count : ℕ),1≤x.m →
    count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
    NativeTime actual x count (A*paperRate x*(coreLog x)^e) := by
  rcases paper_prefix_bound with ⟨A,e,hA⟩
  exact ⟨A,e,fun x count hm he => native_time actual x count _ he (hA x count hm he)⟩

theorem paper_models_and_capacity {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ Ar er Ab eb : ℕ,∀ (x : Input) (firstReciprocal : Bool) (count : ℕ),1≤x.m →
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      NativeTime actual x count (Ar*paperRate x*(coreLog x)^er) ∧
      GeneralPaperSharpSourceBitContract.NativeTime actual C d x count
        (Ab*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^eb) ∧
      GeneralPaperLogarithmicSourceContract.Core actual C d x firstReciprocal count ∧
      OutputAgreement actual x count (GeneralPaperLogarithmicSourceReference.width C d x) := by
  rcases paper_time_bound actual with ⟨Ar,er,hr⟩
  rcases GeneralPaperSharpSourceBitContract.paper_time_and_capacity hg with ⟨Ab,eb,hb⟩
  refine ⟨Ar,er,Ab,eb,?_⟩
  intro x first count hm he
  exact ⟨hr x count hm he,(hb x first count hm he).1,(hb x first count hm he).2,
    same_output actual x count _ he⟩

end Blotto.GeneralPaperSharpSourceRealContract
