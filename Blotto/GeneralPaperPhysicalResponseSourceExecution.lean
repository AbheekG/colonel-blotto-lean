import Blotto.GeneralPaperPhysicalResponseOuterEpoch

/-! The checked source executes each epoch once and appends its returned
candidate rows once. One borrowed physical shift serves the entire loop;
the accumulated flag covers every response in every reached epoch. -/
namespace Blotto.GeneralPaperPhysicalResponseSourceExecution
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def step {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ) (previous : (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) :
    ((Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) × ℕ :=
  let next := GeneralPaperPhysicalResponseOuterEpoch.run bits index model W k Qv a c hc shared delta previous.1.1
  let appended := GeneralPaperTrajectoryAppendExecution.run bits index W shared.trajectory.rows previous.1.2 next.1.1.2
  let A := if bits then arrayWord W (shared.trajectory.epochs+2) else W
  (((next.1.1.1,appended.1),previous.2 && next.1.2),
    next.2+appended.2+GeneralPaperLocalEpochExecution.control index A (count+1)+32*A)

def run {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) : ℕ → ((Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) × ℕ :=
  Nat.rec (by exact
    let forest := GeneralPaperForestInitialPrice.run bits index W m a.lambda
    let A := if bits then arrayWord W (shared.trajectory.rows+2) else W
    (((forest.1,#[]),true),forest.2+PaperIndexedArrayConstruction.initialWork index A shared.trajectory.rows+
      GeneralPaperIntegerWordPrice.compare index 0 0+64*A)) (fun count previous =>
    let next := step bits index model W k Qv a c hc shared delta count previous.1
    (next.1,previous.2+next.2))

theorem run_succ {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ) :
    run bits index model W k Qv a c hc shared delta (count+1)=
      let previous := run bits index model W k Qv a c hc shared delta count
      let next := step bits index model W k Qv a c hc shared delta count previous.1
      (next.1,previous.2+next.2) := rfl

theorem step_base {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ) (previous : (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) :
    (step bits index model W k Qv a c hc shared delta count previous).1.1=
      (GeneralPaperGeometricSourceExecution.step bits index model W k Qv a c hc shared count previous.1).1 := by
  unfold step GeneralPaperGeometricSourceExecution.step
  dsimp only
  rw [GeneralPaperPhysicalResponseOuterEpoch.base_data]

theorem base_data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ) :
    (run bits index model W k Qv a c hc shared delta count).1.1=
      (GeneralPaperGeometricSourceExecution.run bits index model W k Qv a c hc shared count).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [run_succ,GeneralPaperGeometricSourceExecution.run_succ]
    dsimp only
    rw [step_base,ih]

theorem data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (run bits index model W k Qv a c hc shared delta count).1.1=GeneralPaperCatalogueOuterLoop.execute shared a k count := by
  dsimp only
  rw [base_data]
  exact GeneralPaperGeometricSourceExecution.data bits index model W k Qv a c hc weights Bc Br count he

theorem checked {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv q qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (hm : 0<m) (hQv : 0<Qv) (hq : 0<q) (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv)
    (hB : 0≤Br) (hDen : Br.den∣q)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (run bits index model W k Qv a c hc shared (GeneralPaperTagBudgetTransfer.shift m qbar a.C) count).1.2=true := by
  let shared := prepare a k Qv weights Bc Br
  let delta := GeneralPaperTagBudgetTransfer.shift m qbar a.C
  change (run bits index model W k Qv a c hc shared delta count).1.2=true
  induction count with
  | zero => rfl
  | succ count ih =>
    have hi := ih (by omega)
    have hs := congrArg Prod.fst (data bits index model W k Qv a c hc weights Bc Br delta count (by omega))
    have hn := GeneralPaperPhysicalResponseOuterEpoch.checked bits index model W k Qv q qbar a c hc weights Bc Br count
      hm hQv hq hCap hw hB hDen he
    rw [run_succ]
    unfold step
    dsimp only
    rw [hi,Bool.true_and,hs]
    exact hn

def bitExtra (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) (shared : Shared m) : ℕ :=
  shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.bitProfile model W m qbar t a+
    128*W+32*arrayWord W (shared.trajectory.period+2))+64*W+32*arrayWord W (shared.trajectory.epochs+2)

def arithmeticExtra {m : ℕ} (a : Alphabet) (shared : Shared m) : ℕ :=
  shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.arithmeticProfile m a+160)+96

theorem step_bit_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ) (previous : (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool)
    (hSpan : shared.profit.parameters.leafCount=2^shared.profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C)) (hBr : RationalHeight shared.Br t) :
    (step true (fun w => w) model W k Qv a c hc shared delta count previous).2≤
      (GeneralPaperGeometricSourceExecution.step true (fun w => w) model W k Qv a c hc shared count previous.1).2+
      bitExtra model W m qbar t a shared := by
  have h := GeneralPaperPhysicalResponseOuterEpoch.bit_extra model W k Qv qbar t a c hc shared delta previous.1.1 hSpan hd hBr
  unfold step GeneralPaperGeometricSourceExecution.step bitExtra
  dsimp only
  rw [GeneralPaperPhysicalResponseOuterEpoch.base_data]
  simp only [ite_true]
  nlinarith only [h]

theorem bit_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ)
    (hSpan : shared.profit.parameters.leafCount=2^shared.profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C)) (hBr : RationalHeight shared.Br t) :
    (run true (fun w => w) model W k Qv a c hc shared delta count).2≤
      (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hc shared count).2+
      count*bitExtra model W m qbar t a shared := by
  induction count with
  | zero =>
    simp only [Nat.zero_mul,Nat.add_zero]
    exact le_refl _
  | succ count ih =>
    have h := step_bit_extra model W k Qv qbar t a c hc shared delta count
      (run true (fun w => w) model W k Qv a c hc shared delta count).1 hSpan hd hBr
    rw [base_data] at h
    rw [run_succ,GeneralPaperGeometricSourceExecution.run_succ]
    dsimp only
    nlinarith only [ih,h]

theorem step_arithmetic_extra {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ) (previous : (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) :
    (step false (fun _ => 1) model 1 k Qv a c hc shared delta count previous).2≤
      (GeneralPaperGeometricSourceExecution.step false (fun _ => 1) model 1 k Qv a c hc shared count previous.1).2+
      arithmeticExtra a shared := by
  have h := GeneralPaperPhysicalResponseOuterEpoch.arithmetic_extra model k Qv a c hc shared delta previous.1.1
  unfold step GeneralPaperGeometricSourceExecution.step arithmeticExtra
  dsimp only
  rw [GeneralPaperPhysicalResponseOuterEpoch.base_data]
  simp only [Bool.false_eq_true,ite_false,Nat.mul_one]
  nlinarith only [h]

theorem arithmetic_extra {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (count : ℕ) :
    (run false (fun _ => 1) model 1 k Qv a c hc shared delta count).2≤
      (GeneralPaperGeometricSourceExecution.run false (fun _ => 1) model 1 k Qv a c hc shared count).2+
      count*arithmeticExtra a shared := by
  induction count with
  | zero =>
    simp only [Nat.zero_mul,Nat.add_zero]
    exact le_refl _
  | succ count ih =>
    have h := step_arithmetic_extra model k Qv a c hc shared delta count
      (run false (fun _ => 1) model 1 k Qv a c hc shared delta count).1
    rw [base_data] at h
    rw [run_succ,GeneralPaperGeometricSourceExecution.run_succ]
    dsimp only
    nlinarith only [ih,h]

end Blotto.GeneralPaperPhysicalResponseSourceExecution
