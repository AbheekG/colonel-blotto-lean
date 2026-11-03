import Blotto.GeneralPaperActualFieldUpdatePrice

/-! Full indexed all-field round-update prices. Actual reached callbacks
derive every length, code, snapshot and level premise. Both models return
the native next State; row selection and recording are separate components.
-/
namespace Blotto.GeneralPaperRoundFieldsPrice
open GeneralPaperRoundFieldsExecution
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  m*(GeneralPaperFieldUpdateExecution.profile price W m lambda k Qv (GeneralPaperBatchCounterPrice.limit k)+32*W)+
    44*(m+1)*arrayWord W m+64*W

def arithmeticProfile (m k : ℕ) : ℕ :=
  m*(GeneralPaperFieldUpdateExecution.arithmeticProfile k (GeneralPaperBatchCounterPrice.limit k)+32)+44*(m+1)+64

theorem element_work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    let state := stateAt current time
    let before := beforeAt current time
    let rows := rowsAt current time
    let mesh := c.controls.source.meshDenominator
    (element true (fun w => w) model.rat W mesh state before rows j).2≤
      GeneralPaperFieldUpdateExecution.profile model.rat W m cache.alphabet.lambda k Qv (GeneralPaperBatchCounterPrice.limit k)+32*W ∧
    (element false (fun _ => 1) model.rat 1 mesh state before rows j).2≤
      GeneralPaperFieldUpdateExecution.arithmeticProfile k (GeneralPaperBatchCounterPrice.limit k)+32 := by
  have h := GeneralPaperActualFieldUpdatePrice.work model W Qv cache c hc hCodes weights Bc Br time ht j
  exact ⟨Nat.add_le_add_right h.1 _,Nat.add_le_add_right h.2 _⟩

theorem work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let current := selected cache Qv weights Bc Br
    let state := stateAt current time
    let before := beforeAt current time
    let rows := rowsAt current time
    let mesh := c.controls.source.meshDenominator
    (run true (fun w => w) model.rat W mesh state before rows).2≤profile model.rat W m cache.alphabet.lambda k Qv ∧
    (run false (fun _ => 1) model.rat 1 mesh state before rows).2≤arithmeticProfile m k := by
  have he := fun j => element_work model W Qv cache c hc hCodes weights Bc Br time ht j
  have hb := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) _
    (element true (fun w => w) model.rat W c.controls.source.meshDenominator _ _ _)
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m) (fun j => (he j).1)
  have hu := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _
    (element false (fun _ => 1) model.rat 1 c.controls.source.meshDenominator _ _ _)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun j => (he j).2)
  refine ⟨Nat.add_le_add_right hb _,?_⟩
  have h := Nat.add_le_add_right hu 64
  simpa only [run,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticProfile] using h

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) :
    let current := selected cache Qv weights Bc Br
    (run bits index price W c.controls.source.meshDenominator (stateAt current time) (beforeAt current time) (rowsAt current time)).1=
      stateAt current (time+1) := by
  let current := selected cache Qv weights Bc Br
  exact round_data bits index price W _ cache current.powers current.profit current.T weights Bc Br
    (stateAt current time) (by rw [hc]; rfl)

theorem returned_cap {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    GeneralPaperEpochFieldState.Bounded
      ((run bits index price W c.controls.source.meshDenominator (stateAt current time) (beforeAt current time) (rowsAt current time)).1.fields.read j)
        (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) := by
  dsimp only
  rw [data bits index price W Qv cache c hc]
  exact selected_cap cache Qv weights Bc Br (time+1) ht j

theorem same_data {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) :
    let current := selected cache Qv weights Bc Br
    (run true (fun w => w) model.rat W c.controls.source.meshDenominator (stateAt current time) (beforeAt current time) (rowsAt current time)).1=
      (run false (fun _ => 1) model.rat 1 c.controls.source.meshDenominator (stateAt current time) (beforeAt current time) (rowsAt current time)).1 := by
  dsimp only
  rw [data true (fun w => w) model.rat W Qv cache c hc,data false (fun _ => 1) model.rat 1 Qv cache c hc]

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let current := epochRun shared a k trees
    let mesh := c.controls.source.meshDenominator
    (run true (fun w => w) model.rat W mesh (stateAt current time) (beforeAt current time) (rowsAt current time)).2≤
      profile model.rat W m a.lambda k Qv ∧
    (run false (fun _ => 1) model.rat 1 mesh (stateAt current time) (beforeAt current time) (rowsAt current time)).2≤arithmeticProfile m k := by
  dsimp only
  rw [epochRun_selected]
  exact work model W Qv _ c hc (GeneralPaperCatalogueOuterValidity.cache_codes a k Qv weights Bc Br epoch) weights Bc Br time ht

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let current := epochRun shared a k trees
    let mesh := ready.2.source.controls.source.meshDenominator
    (run true (fun w => w) model.rat W mesh (stateAt current time) (beforeAt current time) (rowsAt current time)).2≤profile model.rat W m a.lambda k Qv ∧
    (run false (fun _ => 1) model.rat 1 mesh (stateAt current time) (beforeAt current time) (rowsAt current time)).2≤arithmeticProfile m k := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl weights Bc Br epoch time ht

end Blotto.GeneralPaperRoundFieldsPrice
