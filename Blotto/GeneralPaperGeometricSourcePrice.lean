import Blotto.GeneralPaperGeometricSourceLoopPrice

/-! Complete geometric source prices, after one retained shared preparation.
All steps are joined to their actual reached forests and row arrays. Global
reference W and literal budget words remain explicit pending their joins. -/
namespace Blotto.GeneralPaperGeometricSourcePrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperGeometricSourceExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def initialProfile (W m lambda k : ℕ) : ℕ :=
  GeneralPaperForestInitialPrice.profile W m lambda+256*arrayWord W ((GeneralPaperTrajectoryParameters.prepare lambda k).rows+2)

def profile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) (Bc Br : ℚ) (count : ℕ) : ℕ :=
  initialProfile W m a.lambda k+count*GeneralPaperGeometricSourceStepPrice.profile model W m k Qv a Bc Br

def arithmeticProfile (m k Qv : ℕ) (a : Alphabet) (count : ℕ) : ℕ :=
  (GeneralPaperForestInitialPrice.arithmeticProfile m+256)+count*GeneralPaperGeometricSourceStepPrice.arithmeticProfile m k Qv a

theorem initial_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    let shared := prepare a k Qv weights Bc Br
    (run true (fun x => x) model W k Qv a c hc shared 0).2≤ initialProfile W m a.lambda k ∧
    (run false (fun _ => 1) model 1 k Qv a c hc shared 0).2≤GeneralPaperForestInitialPrice.arithmeticProfile m+256 := by
  let capacity := (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
  have hf := GeneralPaperForestInitialPrice.work W m a.lambda
  have hi := GeneralPaperLocalEpochControlPrice.initial (fun x => x) (fun _ _ h => h) (arrayWord W (capacity+2)) capacity
    (GeneralPaperSummaryArrayControls.array_word_positive W (capacity+2)) (GeneralPaperLocalEpochPrice.capacity_word W capacity)
  have hu := GeneralPaperLocalEpochControlPrice.initial (fun _ => 1) (fun _ _ _ => Nat.le_refl _) 1 capacity (Nat.le_refl _) (Nat.le_refl _)
  constructor
  · change (GeneralPaperForestInitialPrice.run true (fun x => x) W m a.lambda).2+
      PaperIndexedArrayConstruction.initialWork (fun x => x) (arrayWord W (capacity+2)) capacity+
      GeneralPaperIntegerWordPrice.compare (fun x => x) 0 0+64*arrayWord W (capacity+2)≤
        GeneralPaperForestInitialPrice.profile W m a.lambda+256*arrayWord W (capacity+2)
    nlinarith only [hf.1,hi]
  · change (GeneralPaperForestInitialPrice.run false (fun _ => 1) 1 m a.lambda).2+
      PaperIndexedArrayConstruction.initialWork (fun _ => 1) 1 capacity+
      GeneralPaperIntegerWordPrice.compare (fun _ => 1) 0 0+64*1≤GeneralPaperForestInitialPrice.arithmeticProfile m+256
    nlinarith only [hf.2,hu]

theorem work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (run true (fun x => x) model W k Qv a c hc shared count).2≤profile model W m k Qv a Bc Br count ∧
    (run false (fun _ => 1) model 1 k Qv a c hc shared count).2≤arithmeticProfile m k Qv a count := by
  let shared := prepare a k Qv weights Bc Br
  have hbSteps : ∀ time<count,(step true (fun x => x) model W k Qv a c hc shared time
      (run true (fun x => x) model W k Qv a c hc shared time).1).2≤
      GeneralPaperGeometricSourceStepPrice.profile model W m k Qv a Bc Br := by
    intro time ht
    rw [GeneralPaperGeometricSourceExecution.data true (fun x => x) model W k Qv a c hc weights Bc Br time (by omega)]
    exact (GeneralPaperGeometricSourceStepPrice.work model W k Qv a c hc weights Bc Br hWeights time (by omega)).1
  have huSteps : ∀ time<count,(step false (fun _ => 1) model 1 k Qv a c hc shared time
      (run false (fun _ => 1) model 1 k Qv a c hc shared time).1).2≤
      GeneralPaperGeometricSourceStepPrice.arithmeticProfile m k Qv a := by
    intro time ht
    rw [GeneralPaperGeometricSourceExecution.data false (fun _ => 1) model 1 k Qv a c hc weights Bc Br time (by omega)]
    exact (GeneralPaperGeometricSourceStepPrice.work model W k Qv a c hc weights Bc Br hWeights time (by omega)).2
  have hi := initial_work model W k Qv a c hc weights Bc Br
  exact ⟨GeneralPaperGeometricSourceLoopPrice.work true (fun x => x) model W k Qv a c hc shared _ _ count hi.1 hbSteps,
    GeneralPaperGeometricSourceLoopPrice.work false (fun _ => 1) model 1 k Qv a c hc shared _ _ count hi.2 huSteps⟩

theorem complete_rows {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    let shared := prepare a k Qv weights Bc Br
    (run bits index model W k Qv a c hc shared shared.trajectory.epochs).1.2.size=shared.trajectory.rows := by
  dsimp only
  erw [GeneralPaperGeometricSourceExecution.size bits index model W k Qv a c hc weights Bc Br _ (Nat.le_refl _)]
  rfl

end Blotto.GeneralPaperGeometricSourcePrice
