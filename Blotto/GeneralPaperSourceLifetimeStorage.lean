import Blotto.GeneralPaperEpochSourcePhaseStorage

/-! Structural lifetime observer of the complete native outer source.
It preserves the exact returned forest and full pre-update trajectory.
Only control frames accumulate across recursive calls; each epoch's cache
and temporaries end before the following epoch. Appending retains the actual
old/chunk/new owners. Global W and backend/paper asymptotics remain explicit. -/
namespace Blotto.GeneralPaperSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

def initialPeak (W m lambda : ℕ) : ℕ :=
  maximum (fun count : Fin (m+1) => GeneralPaperInitialForestConstructionStorage.window W m lambda count.val (Nat.le_of_lt_succ count.isLt))

theorem initial_bound (W m lambda : ℕ) : initialPeak W m lambda≤GeneralPaperInitialForestConstructionStorage.profile W m lambda :=
  maximum_bound _ _ (fun count => GeneralPaperInitialForestConstructionStorage.bounded W m lambda count.val (Nat.le_of_lt_succ count.isLt))

def initialOwner (W m lambda : ℕ) : ℕ :=
  GeneralPaperEncodedForestStorage.footprint W (GeneralPaperForestInitialPrice.run true (fun w => w) W m lambda).1

theorem initial_owner_bound {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    initialOwner W m a.lambda≤GeneralPaperEncodedForestStorage.profile W m a.lambda k Qv := by
  have h := GeneralPaperEncodedForestStorage.actual W k Qv a weights Bc Br 0 (Nat.zero_le _)
  rw [initialOwner,GeneralPaperForestInitialPrice.data]
  exact h

def returnedWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let value := (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hc shared count).1
  GeneralPaperEncodedForestStorage.footprint W value.1+
    GeneralPaperEncodedTrajectoryStorage.footprint W shared.trajectory.rows value.2+64*W

def returnedProfile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperEncodedForestStorage.profile W m lambda k Qv+GeneralPaperEncodedTrajectoryStorage.profile W m lambda k+64*W

theorem returned_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    returnedWindow model W k Qv a c hc weights Bc Br count≤returnedProfile W m a.lambda k Qv := by
  have hf := GeneralPaperEncodedForestStorage.actual W k Qv a weights Bc Br count he
  have hr := GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights Bc Br count he
  unfold returnedWindow
  dsimp only
  rw [GeneralPaperGeometricSourceExecution.data true (fun w => w) model W k Qv a c hc weights Bc Br count he]
  exact Nat.add_le_add_right (Nat.add_le_add hf hr) _

def appendWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (count : Fin ((GeneralPaperTrajectoryParameters.prepare a.lambda k).period+1)) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let first := (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hc shared epoch).1.2
  let chunk := (GeneralPaperOuterEpochExecution.run true (fun w => w) model W k Qv a c hc shared (treesAt shared a k epoch)).1.2
  GeneralPaperTrajectoryAppendStorage.window W shared.trajectory.rows first chunk (min count.val chunk.size) (Nat.min_le_right ..)

def appendPeak {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  maximum (appendWindow model W k Qv a c hc weights Bc Br epoch)

def appendProfile (W m lambda k : ℕ) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  GeneralPaperTrajectoryAppendStorage.profile W m t.rows t.period (GeneralPaperDecoderControls.operandWidth lambda)

theorem append_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    appendPeak model W k Qv a c hc weights Bc Br epoch≤appendProfile W m a.lambda k := by
  apply maximum_bound
  intro count
  let shared := prepare a k Qv weights Bc Br
  let chunk := (GeneralPaperOuterEpochExecution.run true (fun w => w) model W k Qv a c hc shared (treesAt shared a k epoch)).1.2
  have hcount : min count.val chunk.size≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period :=
    (Nat.min_le_left ..).trans (Nat.le_of_lt_succ count.isLt)
  exact GeneralPaperActualSourceTrajectoryStorage.native_append model W k Qv a c hc weights Bc Br epoch _ he hcount (Nat.min_le_right ..)

def base (W m lambda k : ℕ) : ℕ :=
  let T := (GeneralPaperTrajectoryParameters.prepare lambda k).rows
  initialPeak W m lambda+GeneralPaperTrajectoryControllerStorage.base W T+
    GeneralPaperEncodedTrajectoryStorage.footprint W T (#[] : Array (FixedArrayTable m ℕ))+128*W

def baseProfile (W m lambda k : ℕ) : ℕ :=
  let T := (GeneralPaperTrajectoryParameters.prepare lambda k).rows
  GeneralPaperInitialForestConstructionStorage.profile W m lambda+
    256*GeneralPaperSummaryArrayExecution.arrayWord W (T+2)+T*W+192*W

theorem base_bound (W m lambda k : ℕ) : base W m lambda k≤baseProfile W m lambda k := by
  have hi := initial_bound W m lambda
  have hb := GeneralPaperTrajectoryControllerStorage.base_bound W (GeneralPaperTrajectoryParameters.prepare lambda k).rows
  have he : GeneralPaperEncodedTrajectoryStorage.footprint W (GeneralPaperTrajectoryParameters.prepare lambda k).rows
      (#[] : Array (FixedArrayTable m ℕ))=(GeneralPaperTrajectoryParameters.prepare lambda k).rows*W+64*W := by
    simp only [GeneralPaperEncodedTrajectoryStorage.footprint,GeneralPaperRetainedTrajectoryBits.trajectoryBits,
      Array.size_empty,Finset.univ_eq_empty,Finset.sum_empty,Nat.zero_mul,Nat.zero_add]
  dsimp only [base,baseProfile]
  omega

def phase {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) : ℕ :=
  returnedWindow model W k Qv a c hc weights Bc Br epoch+
    max (GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch)
      (appendPeak model W k Qv a c hc weights Bc Br epoch+returnedWindow model W k Qv a c hc weights Bc Br (epoch+1))+
    GeneralPaperLocalEpochExecution.control (fun w => w)
      (GeneralPaperSummaryArrayExecution.arrayWord W ((GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+2)) (epoch+1)+256*W

def phaseProfile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  returnedProfile W m a.lambda k Qv+
    max (GeneralPaperEpochSourcePhaseStorage.profile model W k Qv a weights Bc Br)
      (appendProfile W m a.lambda k+returnedProfile W m a.lambda k Qv)+
    131*GeneralPaperSummaryArrayExecution.arrayWord W ((GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+2)+256*W

theorem phase_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    phase model W k Qv a c hc weights Bc Br epoch≤phaseProfile model W k Qv a weights Bc Br := by
  have hold := returned_bound model W k Qv a c hc weights Bc Br epoch (by omega)
  have hnext := returned_bound model W k Qv a c hc weights Bc Br (epoch+1) he
  have hepoch := GeneralPaperEpochSourcePhaseStorage.bounded model W k Qv a c hc weights Bc Br hw epoch he
  have happend := append_bound model W k Qv a c hc weights Bc Br epoch he
  have hcontrol := GeneralPaperLocalEpochControlPrice.control (fun w => w) (fun _ _ h => h)
    (GeneralPaperSummaryArrayExecution.arrayWord W ((GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs+2))
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs (epoch+1) (by omega)
    (GeneralPaperLocalEpochPrice.capacity_word W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hold (max_le_max hepoch (Nat.add_le_add happend hnext))) hcontrol) _

def observe {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    ℕ → (GeneralPaperCatalogueTreeCache.Trees m a.lambda × Array (FixedArrayTable m ℕ)) × ℕ :=
  Nat.rec (((GeneralPaperForestInitialPrice.run true (fun w => w) W m a.lambda).1,#[]),base W m a.lambda k)
    (fun epoch previous =>
    let next := GeneralPaperGeometricSourceExecution.step true (fun w => w) model W k Qv a c hc
      (prepare a k Qv weights Bc Br) epoch previous.1
    (next.1,GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs (epoch+1)+
      max previous.2 (phase model W k Qv a c hc weights Bc Br epoch)))

theorem observe_succ {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    observe model W k Qv a c hc weights Bc Br (epoch+1)=
      let previous := observe model W k Qv a c hc weights Bc Br epoch
      let next := GeneralPaperGeometricSourceExecution.step true (fun w => w) model W k Qv a c hc
        (prepare a k Qv weights Bc Br) epoch previous.1
      (next.1,GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs (epoch+1)+
        max previous.2 (phase model W k Qv a c hc weights Bc Br epoch)) := rfl

theorem native_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    (observe model W k Qv a c hc weights Bc Br count).1=
      (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hc (prepare a k Qv weights Bc Br) count).1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [observe_succ,GeneralPaperGeometricSourceExecution.run_succ,ih]

theorem peak_identity {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    (observe model W k Qv a c hc weights Bc Br count).2=
      scopePeak (base W m a.lambda k)
        (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
        (phase model W k Qv a c hc weights Bc Br) count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [observe_succ,scopePeak,ih]

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) : ℕ :=
  initialOwner W m a.lambda+(observe model W k Qv a c hc weights Bc Br count).2+
    returnedWindow model W k Qv a c hc weights Bc Br count+128*W

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let E := (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs
  GeneralPaperEncodedForestStorage.profile W m a.lambda k Qv+E*GeneralPaperTrajectoryControllerStorage.frameProfile W E+
    max (baseProfile W m a.lambda k) (phaseProfile model W k Qv a weights Bc Br)+returnedProfile W m a.lambda k Qv+128*W

theorem bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    window model W k Qv a c hc weights Bc Br count≤profile model W k Qv a weights Bc Br := by
  let B := max (baseProfile W m a.lambda k) (phaseProfile model W k Qv a weights Bc Br)
  have hi := initial_owner_bound W k Qv a weights Bc Br
  have hb : base W m a.lambda k≤B := (base_bound W m a.lambda k).trans (Nat.le_max_left ..)
  have hp : ∀ i<count,phase model W k Qv a c hc weights Bc Br i≤B := fun i hit =>
    (phase_bound model W k Qv a c hc weights Bc Br hw i (by omega)).trans (Nat.le_max_right ..)
  have hs := scoped_bound (base W m a.lambda k) B
    (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (phase model W k Qv a c hc weights Bc Br) count hb hp
  have hf := stack_bound (GeneralPaperTrajectoryControllerStorage.frame W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (GeneralPaperTrajectoryControllerStorage.frameProfile W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) count
    (fun i hit => GeneralPaperTrajectoryControllerStorage.frame_bound W _ i (by omega))
  have hmul := Nat.mul_le_mul_right (GeneralPaperTrajectoryControllerStorage.frameProfile W
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) he
  have hr := returned_bound model W k Qv a c hc weights Bc Br count he
  unfold window
  rw [peak_identity]
  dsimp only [profile,B] at *
  omega

end Blotto.GeneralPaperSourceLifetimeStorage
