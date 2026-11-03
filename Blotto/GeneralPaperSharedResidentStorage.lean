import Blotto.GeneralPaperEncodedSharedSource

/-! One-time native Shared data coexist with the reached resident core.
This closes the retained native Shared contribution, not all temporary
construction/traversal workspaces or the global reference-word theorem. -/
namespace Blotto.GeneralPaperSharedResidentStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem actual {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    GeneralPaperEncodedSharedSource.footprint W (prepare a k Qv weights Bc Br)+
      GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time≤
    GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br+
      GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv :=
  Nat.add_le_add (GeneralPaperEncodedSharedSource.native W k Qv a weights Bc Br)
    (GeneralPaperEpochResidentStorage.actual W k Qv a weights Bc Br epoch time he ht)

theorem retained_first_trajectory {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ)
    (Bc Br firstBc firstBr : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      (GeneralPaperEncodedSharedSource.footprint W (prepare a k Qv weights Bc Br)+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)≤
    GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+
      (GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br+
        GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv) :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual W k Qv a weights Bc Br epoch time he ht)

end Blotto.GeneralPaperSharedResidentStorage
