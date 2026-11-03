import Blotto.GeneralPaperGeometricSourceExecution

/-! Price one actual source step, deriving append capacities from the
returned epoch length and the retained total number of trajectory rows. -/
namespace Blotto.GeneralPaperGeometricSourceStepPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) (Bc Br : ℚ) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare a.lambda k
  GeneralPaperOuterEpochPrice.profile model W m k Qv a Bc Br+
    GeneralPaperTrajectoryAppendPrice.profile W t.rows t.period+256*arrayWord W (t.epochs+2)

def arithmeticProfile (m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperOuterEpochPrice.arithmeticProfile m k Qv a+
    GeneralPaperTrajectoryAppendPrice.arithmeticProfile (GeneralPaperTrajectoryParameters.prepare a.lambda k).period+256

theorem chunk_size {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k count
    (GeneralPaperOuterEpochExecution.run bits index model W k Qv a c hc shared trees).1.2.size=shared.trajectory.period := by
  dsimp only
  rw [GeneralPaperOuterEpochExecution.data bits index model W k Qv a c hc weights Bc Br count he,
    GeneralPaperCatalogueOuterLoop.epoch_size]

theorem append_capacity {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let previous := GeneralPaperCatalogueOuterLoop.execute shared a k count
    previous.2.size+(GeneralPaperOuterEpochExecution.run bits index model W k Qv a c hc shared previous.1).1.2.size≤shared.trajectory.rows := by
  dsimp only
  erw [GeneralPaperCatalogueOuterLoop.trajectory_size,chunk_size bits index model W k Qv a c hc weights Bc Br count he]
  change count*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+(GeneralPaperTrajectoryParameters.prepare a.lambda k).period≤
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  calc
    _=(count+1)*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period := by ring
    _≤_ := Nat.mul_le_mul_right _ he

theorem work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let previous := GeneralPaperCatalogueOuterLoop.execute shared a k count
    (GeneralPaperGeometricSourceExecution.step true (fun x => x) model W k Qv a c hc shared count previous).2≤profile model W m k Qv a Bc Br ∧
    (GeneralPaperGeometricSourceExecution.step false (fun _ => 1) model 1 k Qv a c hc shared count previous).2≤arithmeticProfile m k Qv a := by
  let shared := prepare a k Qv weights Bc Br
  let previous := GeneralPaperCatalogueOuterLoop.execute shared a k count
  let t := GeneralPaperTrajectoryParameters.prepare a.lambda k
  have hn := GeneralPaperOuterEpochPrice.work model W k Qv a c hc weights Bc Br hWeights count he
  have hb := (GeneralPaperTrajectoryAppendPrice.work W t.rows previous.2
    (GeneralPaperOuterEpochExecution.run true (fun x => x) model W k Qv a c hc shared previous.1).1.2
    (append_capacity true (fun x => x) model W k Qv a c hc weights Bc Br count he)).1
  have hu := (GeneralPaperTrajectoryAppendPrice.work 1 t.rows previous.2
    (GeneralPaperOuterEpochExecution.run false (fun _ => 1) model 1 k Qv a c hc shared previous.1).1.2
    (append_capacity false (fun _ => 1) model 1 k Qv a c hc weights Bc Br count he)).2
  erw [chunk_size true (fun x => x) model W k Qv a c hc weights Bc Br count he] at hb
  erw [chunk_size false (fun _ => 1) model 1 k Qv a c hc weights Bc Br count he] at hu
  change _≤GeneralPaperTrajectoryAppendPrice.profile W t.rows t.period at hb
  change _≤GeneralPaperTrajectoryAppendPrice.arithmeticProfile t.period at hu
  have he' : count+1≤t.epochs := he
  have hcb := GeneralPaperLocalEpochControlPrice.control (fun x => x) (fun _ _ h => h) (arrayWord W (t.epochs+2)) t.epochs (count+1)
    (he'.trans (Nat.le_succ _)) (GeneralPaperLocalEpochPrice.capacity_word W t.epochs)
  have hcu := GeneralPaperLocalEpochControlPrice.control (fun _ => 1) (fun _ _ _ => Nat.le_refl _) 1 t.epochs (count+1) (he'.trans (Nat.le_succ _)) (Nat.le_refl _)
  constructor
  · have h := Nat.add_le_add (Nat.add_le_add hn.1 hb) hcb
    apply h.trans
    change _≤GeneralPaperOuterEpochPrice.profile model W m k Qv a Bc Br+GeneralPaperTrajectoryAppendPrice.profile W t.rows t.period+256*arrayWord W (t.epochs+2)
    omega
  · have h := Nat.add_le_add (Nat.add_le_add hn.2 hu) hcu
    apply h.trans
    change _≤GeneralPaperOuterEpochPrice.arithmeticProfile m k Qv a+GeneralPaperTrajectoryAppendPrice.arithmeticProfile t.period+256
    omega

end Blotto.GeneralPaperGeometricSourceStepPrice
