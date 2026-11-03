import Blotto.GeneralPaperRoundPhaseStorage

/-! A structural observer of the native local loop. It returns exactly the
same states and candidate-row prefixes. Only caller frames accumulate across
recursion; round temporaries end at the call boundary. The retained initial
state and complete returned/push buffers are counted outside that maximum.
The observer erases and is not a second source execution. -/
namespace Blotto.GeneralPaperLocalSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperEncodedScalarStorage GeneralPaperFiniteStorageWindows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

def cache {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :=
  GeneralPaperCatalogueShared.cache (prepare a k Qv weights Bc Br) a k
    (GeneralPaperCatalogueOuterLoop.treesAt (prepare a k Qv weights Bc Br) a k epoch)

def current {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :=
  selected (cache a k Qv weights Bc Br epoch) Qv weights Bc Br

def initialWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (cursor : Fin (m+1) × Fin (GeneralPaperRoundPhaseStorage.progressCap m a.lambda k Qv+1)) : ℕ :=
  GeneralPaperEpochInitialConstructionStorage.familyWindow model W (cache a k Qv weights Bc Br epoch)
    cursor.1.val cursor.2.val (Nat.le_of_lt_succ cursor.1.isLt)

def initialPeak {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  maximum (initialWindow model W k Qv a weights Bc Br epoch)

theorem initial_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    initialPeak model W k Qv a weights Bc Br epoch≤GeneralPaperEpochInitialConstructionStorage.familyProfile model W m a.lambda k Qv := by
  apply maximum_bound
  intro cursor
  exact GeneralPaperEpochInitialConstructionStorage.family_bounded model W Qv _ cursor.1.val cursor.2.val
    (Nat.le_of_lt_succ cursor.1.isLt)

def initialOwner {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  GeneralPaperEncodedEpochLevels.familyFootprint W
    (GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W (cache a k Qv weights Bc Br epoch)).1.fields

theorem initial_owner_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    initialOwner model W k Qv a weights Bc Br epoch≤GeneralPaperEncodedEpochLevels.profile W m a.lambda k Qv :=
  GeneralPaperEpochInitialConstructionStorage.family_returned model W Qv _

def returnedWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) : ℕ :=
  let r := current a k Qv weights Bc Br epoch
  let P := (GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  let value := (GeneralPaperLocalEpochExecution.execute true (fun w => w) model.rat W c
    (cache a k Qv weights Bc Br epoch) r.profit r.T weights Bc Br P count).1
  GeneralPaperEncodedEpochLevels.familyFootprint W value.1.fields+GeneralPaperEncodedTrajectoryStorage.footprint W P value.2+64*W

def returnedProfile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperEncodedEpochLevels.profile W m lambda k Qv+GeneralPaperLocalTrajectoryStorage.profile W m lambda k+64*W

theorem returned_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ)
    (ht : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    returnedWindow model W k Qv a c weights Bc Br epoch count≤returnedProfile W m a.lambda k Qv := by
  have hf := GeneralPaperEncodedEpochLevels.selected W Qv (cache a k Qv weights Bc Br epoch) weights Bc Br count ht
  have hr := GeneralPaperLocalTrajectoryStorage.selected W Qv (cache a k Qv weights Bc Br epoch) weights Bc Br count ht
  unfold returnedWindow
  dsimp only [current]
  rw [GeneralPaperSelectedLocalEpochExecution.data true (fun w => w) model.rat W Qv
    (cache a k Qv weights Bc Br epoch) c hc weights Bc Br
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).period count]
  exact Nat.add_le_add_right (Nat.add_le_add hf hr) _

def base {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  let P := (GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  initialPeak model W k Qv a weights Bc Br epoch+GeneralPaperTrajectoryControllerStorage.base W P+
    GeneralPaperEncodedTrajectoryStorage.footprint W P (#[] : Array (FixedArrayTable m ℕ))+128*W

def baseProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let P := (GeneralPaperTrajectoryParameters.prepare lambda k).period
  GeneralPaperEpochInitialConstructionStorage.familyProfile model W m lambda k Qv+
    256*GeneralPaperSummaryArrayExecution.arrayWord W (P+2)+P*W+192*W

theorem base_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    base model W k Qv a weights Bc Br epoch≤baseProfile model W m a.lambda k Qv := by
  have hi := initial_bound model W k Qv a weights Bc Br epoch
  have hb := GeneralPaperTrajectoryControllerStorage.base_bound W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  have he : GeneralPaperEncodedTrajectoryStorage.footprint W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period
      (#[] : Array (FixedArrayTable m ℕ))=(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*W+64*W := by
    simp only [GeneralPaperEncodedTrajectoryStorage.footprint,GeneralPaperRetainedTrajectoryBits.trajectoryBits,
      Array.size_empty,Finset.univ_eq_empty,Finset.sum_empty,Nat.zero_mul,Nat.zero_add]
  dsimp only [base,baseProfile]
  omega

def phase {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) : ℕ :=
  GeneralPaperRoundPhaseStorage.window model W k Qv a c weights Bc Br epoch time+
    returnedWindow model W k Qv a c weights Bc Br epoch (time+1)+
    GeneralPaperTrajectoryControllerStorage.step W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period time+256*W

def phaseProfile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperRoundPhaseStorage.profile model W k Qv a weights Bc Br+returnedProfile W m a.lambda k Qv+
    256*GeneralPaperSummaryArrayExecution.arrayWord W ((GeneralPaperTrajectoryParameters.prepare a.lambda k).period+2)+256*W

theorem phase_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    phase model W k Qv a c weights Bc Br epoch time≤phaseProfile model W k Qv a weights Bc Br :=
  Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
    (GeneralPaperRoundPhaseStorage.bounded model W k Qv a c hc weights Bc Br hw epoch time he ht)
    (returned_bound model W k Qv a c hc weights Bc Br epoch (time+1) ht))
    (GeneralPaperTrajectoryControllerStorage.step_bound W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period time (by omega))) _

def observe {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    ℕ → (GeneralPaperCatalogueEpochCache.State (cache a k Qv weights Bc Br epoch) × Array (FixedArrayTable m ℕ)) × ℕ
  | 0 => (((GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W (cache a k Qv weights Bc Br epoch)).1,#[]),
      base model W k Qv a weights Bc Br epoch)
  | time+1 =>
    let previous := observe model W k Qv a c weights Bc Br epoch time
    let r := current a k Qv weights Bc Br epoch
    let next := GeneralPaperRoundExecution.run true (fun w => w) model.rat W c
      (cache a k Qv weights Bc Br epoch) r.profit r.T weights Bc Br previous.1.1
    ((next.1.state,previous.1.2.push next.1.candidate),
      GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period (time+1)+
        max previous.2 (phase model W k Qv a c weights Bc Br epoch time))

theorem native_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) :
    (observe model W k Qv a c weights Bc Br epoch count).1=
      let r := current a k Qv weights Bc Br epoch
      (GeneralPaperLocalEpochExecution.execute true (fun w => w) model.rat W c
        (cache a k Qv weights Bc Br epoch) r.profit r.T weights Bc Br
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).period count).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [observe,GeneralPaperLocalEpochExecution.execute,GeneralPaperLocalEpochExecution.run] at ih ⊢
    rw [ih]

theorem peak_identity {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) :
    (observe model W k Qv a c weights Bc Br epoch count).2=
      scopePeak (base model W k Qv a weights Bc Br epoch)
        (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
        (phase model W k Qv a c weights Bc Br epoch) count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [observe,scopePeak,ih]

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) : ℕ :=
  initialOwner model W k Qv a weights Bc Br epoch+(observe model W k Qv a c weights Bc Br epoch count).2+
    returnedWindow model W k Qv a c weights Bc Br epoch count+128*W

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let P := (GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  GeneralPaperEncodedEpochLevels.profile W m a.lambda k Qv+P*GeneralPaperTrajectoryControllerStorage.frameProfile W P+
    max (baseProfile model W m a.lambda k Qv) (phaseProfile model W k Qv a weights Bc Br)+
    returnedProfile W m a.lambda k Qv+128*W

theorem bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch count : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    window model W k Qv a c weights Bc Br epoch count≤profile model W k Qv a weights Bc Br := by
  let B := max (baseProfile model W m a.lambda k Qv) (phaseProfile model W k Qv a weights Bc Br)
  have hi := initial_owner_bound model W k Qv a weights Bc Br epoch
  have hb : base model W k Qv a weights Bc Br epoch≤B :=
    (base_bound model W k Qv a weights Bc Br epoch).trans (Nat.le_max_left ..)
  have hp : ∀ i<count,phase model W k Qv a c weights Bc Br epoch i≤B := fun i hit =>
    (phase_bound model W k Qv a c hc weights Bc Br hw epoch i he (by omega)).trans (Nat.le_max_right ..)
  have hs := scoped_bound (base model W k Qv a weights Bc Br epoch) B
    (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (phase model W k Qv a c weights Bc Br epoch) count hb hp
  have hf := stack_bound (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (GeneralPaperTrajectoryControllerStorage.frameProfile W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) count
    (fun i hit => GeneralPaperTrajectoryControllerStorage.frame_bound W _ i (by omega))
  have hmul := Nat.mul_le_mul_right (GeneralPaperTrajectoryControllerStorage.frameProfile W
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) ht
  have hr := returned_bound model W k Qv a c hc weights Bc Br epoch count ht
  unfold window
  rw [peak_identity]
  dsimp only [profile,B] at *
  omega

end Blotto.GeneralPaperLocalSourceLifetimeStorage
