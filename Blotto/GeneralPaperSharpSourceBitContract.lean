import Blotto.GeneralPaperSharpSourceBitRate

/-! The complete original native iterative-source run has the sharp paper
fast-bit rate, at the same derived word as its retained lifetime/address
capacity. No primitive model, dependent cache or returned data is substituted.
Original-game/compiler/final-driver contracts remain separate joins. -/
namespace Blotto.GeneralPaperSharpSourceBitContract
open GeneralPaperSourceWordGrowth GeneralPaperSharpSourceBitRate
open GeneralPaperFastRationalModel GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def NativeTime (actual : RationalCostModel) (C d : ℕ) (x : Input) (count bound : ℕ) : Prop :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let W := GeneralPaperLogarithmicSourceReference.width C d x
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m a.lambda x.k x.Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  (GeneralPaperGeometricSourceExecution.run true (fun w => w) actual W x.k x.Qv a c hc ready.1.2 count).2≤bound

theorem native_time {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (x : Input) (count bound : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
    (hp : GeneralPaperFastSourceMajorant.profile C d (GeneralPaperLogarithmicSourceReference.width C d x)
      x.m x.k x.Qv (alphabet x) count≤bound) : NativeTime actual C d x count bound := by
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let W := GeneralPaperLogarithmicSourceReference.width C d x
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  have ha : a=alphabet x := by
    dsimp only [a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have ht := GeneralPaperFastSourceMajorant.classified_prepared hg W x.k x.Qv x.b x.hb x.reciprocal
    x.weights x.weight_sum count he
  apply ht.trans
  change GeneralPaperFastSourceMajorant.profile C d W x.m x.k x.Qv a count≤bound
  rw [ha]
  exact hp

theorem time_and_capacity {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (firstReciprocal : Bool) (count : ℕ),
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      NativeTime actual C d x count (A*sourceRate x*(logSize x)^e) ∧
      GeneralPaperLogarithmicSourceContract.Core actual C d x firstReciprocal count := by
  rcases common_word_prefix_bound C d with ⟨A,e,hA⟩
  exact ⟨A,e,fun x first count he => ⟨native_time hg x count _ he (hA x count he),
    GeneralPaperLogarithmicSourceContract.native_core hg x first count he⟩⟩

theorem paper_time_and_capacity {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (firstReciprocal : Bool) (count : ℕ),1≤x.m →
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      NativeTime actual C d x count (A*paperRate x*(logSize x)^e) ∧
      GeneralPaperLogarithmicSourceContract.Core actual C d x firstReciprocal count := by
  rcases paper_prefix_bound C d with ⟨A,e,hA⟩
  exact ⟨A,e,fun x first count hm he => ⟨native_time hg x count _ he (hA x count hm he),
    GeneralPaperLogarithmicSourceContract.native_core hg x first count he⟩⟩

end Blotto.GeneralPaperSharpSourceBitContract
