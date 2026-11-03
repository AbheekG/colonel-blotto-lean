import Blotto.GeneralPaperTrajectoryControllerStorage

/-! Actual full pre-update source rows derive every append payload and
capacity premise. Native priced returns transfer through their checked data
identities; no row validation, source replay or selector rerun is executed. -/
namespace Blotto.GeneralPaperActualSourceTrajectoryStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperRetainedTrajectoryBits (rowBits)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem global_rows {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    GeneralPaperTrajectoryAppendStorage.RowsBound (GeneralPaperDecoderControls.operandWidth a.lambda)
      (execute (prepare a k Qv weights Bc Br) a k epoch).2 :=
  fun i => GeneralPaperRetainedTrajectoryBits.row_bound _ _ (GeneralPaperRetainedTrajectoryBits.global_row_word a k Qv weights Bc Br epoch i)

theorem epoch_rows {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda) :
    GeneralPaperTrajectoryAppendStorage.RowsBound (GeneralPaperDecoderControls.operandWidth a.lambda) (GeneralPaperCatalogueOuterLoop.epoch shared a k trees).2 := by
  intro i
  have hi : i.val<shared.trajectory.period := i.isLt.trans_eq (epoch_size shared a k trees)
  change rowBits ((GeneralPaperCatalogueEpoch.execute (cache shared a k trees) shared.powers shared.profit shared.trajectory.rows
    shared.weights shared.Bc shared.Br (GeneralPaperCatalogueEpochCache.initial (cache shared a k trees)) shared.trajectory.period).2[i.val])≤_
  rw [GeneralPaperCatalogueEpoch.trajectory_read _ _ _ _ _ _ _ _ _ _ hi]
  exact GeneralPaperRetainedTrajectoryBits.row_bound _ _ (GeneralPaperRetainedTrajectoryBits.candidate_word _ _ _ _ _ _ _ _)

theorem append_capacity {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (execute shared a k epoch).2.size+(GeneralPaperCatalogueOuterLoop.epoch shared a k (treesAt shared a k epoch)).2.size≤shared.trajectory.rows := by
  dsimp only
  rw [trajectory_size,epoch_size]
  have h := Nat.mul_le_mul_right (GeneralPaperTrajectoryParameters.prepare a.lambda k).period he
  change epoch*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+(GeneralPaperTrajectoryParameters.prepare a.lambda k).period≤
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
  rw [GeneralPaperTrajectoryParameters.rows_product]
  nlinarith only [h]

theorem append {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (hc : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := prepare a k Qv weights Bc Br
    let first := (execute shared a k epoch).2
    let chunk := (GeneralPaperCatalogueOuterLoop.epoch shared a k (treesAt shared a k epoch)).2
    GeneralPaperTrajectoryAppendStorage.window W shared.trajectory.rows first chunk count
      (by rw [epoch_size]; exact hc)≤GeneralPaperTrajectoryAppendStorage.profile W m shared.trajectory.rows shared.trajectory.period
        (GeneralPaperDecoderControls.operandWidth a.lambda) := by
  have h := GeneralPaperTrajectoryAppendStorage.bounded W (prepare a k Qv weights Bc Br).trajectory.rows
    (GeneralPaperDecoderControls.operandWidth a.lambda) (execute (prepare a k Qv weights Bc Br) a k epoch).2
    (GeneralPaperCatalogueOuterLoop.epoch (prepare a k Qv weights Bc Br) a k (treesAt (prepare a k Qv weights Bc Br) a k epoch)).2 count
    (by rw [epoch_size]; exact hc) (append_capacity a k Qv weights Bc Br epoch he)
    (global_rows a k Qv weights Bc Br epoch) (epoch_rows _ a k _)
  exact h.trans_eq (by rw [epoch_size])

theorem native_append {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hcache : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (hc : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := prepare a k Qv weights Bc Br
    let first := (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hcache shared epoch).1.2
    let chunk := (GeneralPaperOuterEpochExecution.run true (fun w => w) model W k Qv a c hcache shared (treesAt shared a k epoch)).1.2
    ∀ h : count≤chunk.size,GeneralPaperTrajectoryAppendStorage.window W shared.trajectory.rows first chunk count h≤
      GeneralPaperTrajectoryAppendStorage.profile W m shared.trajectory.rows shared.trajectory.period (GeneralPaperDecoderControls.operandWidth a.lambda) := by
  dsimp only
  rw [GeneralPaperGeometricSourceExecution.data true (fun w => w) model W k Qv a c hcache weights Bc Br epoch (by omega),
    GeneralPaperOuterEpochExecution.data true (fun w => w) model W k Qv a c hcache weights Bc Br epoch he]
  intro h
  exact append W k Qv a weights Bc Br epoch count he hc

end Blotto.GeneralPaperActualSourceTrajectoryStorage
