import Blotto.GeneralPaperReferenceCapacity
import Blotto.GeneralPaperResidentReferenceScaling

/-! One reference width covers the closed source profile, retained native
front/cache, literal input scales, a completed first trajectory, and the
checked classifier and parameter/power preparation reservations. This is
an erased capacity calibration, not a new parameter or execution pass.
Compiler and final paper soft-O/input-height joins remain separate. -/
namespace Blotto.GeneralPaperPreparedReferenceCapacity
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperReferenceScaling GeneralPaperReferenceCapacity
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def profile {m : ℕ} (model : RationalCostModel) (W k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperPrecallResidentStorage.inputProfile W m k Qv B Hc Hr+
    GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
    GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+
    GeneralPaperSourceLifetimeStorage.profile model W k Qv a weights Bc Br+
    GeneralPaperClassifierConstructionStorage.profile model W m k B+
    GeneralPaperPreparationResidentStorage.constructionProfile model W m a.lambda k Qv

@[fun_prop]
theorem scaling {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile model W k Qv B Hc Hr a weights Bc Br) := by
  fun_prop [profile]

def width {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  referenceWord (profile model 1 k Qv B Hc Hr a weights Bc Br)+GeneralPaperPrecallControlWord.word m k

theorem control_word {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperPrecallControlWord.word m k≤width model k Qv B Hc Hr a weights Bc Br := by
  unfold width
  omega

theorem positive_width {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    1≤width model k Qv B Hc Hr a weights Bc Br := by
  have h := positive (profile model 1 k Qv B Hc Hr a weights Bc Br)
  unfold width
  omega

theorem capacity {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    profile model (width model k Qv B Hc Hr a weights Bc Br) k Qv B Hc Hr a weights Bc Br<
      2^width model k Qv B Hc Hr a weights Bc Br :=
  padded_profile_capacity _ (scaling model k Qv B Hc Hr a weights Bc Br) _

theorem linear_bound {m : ℕ} (model : RationalCostModel) (W k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hW : 1≤W) :
    profile model W k Qv B Hc Hr a weights Bc Br≤W*profile model 1 k Qv B Hc Hr a weights Bc Br :=
  at_one _ (scaling model k Qv B Hc Hr a weights Bc Br) W hW

theorem address_width {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (address : ℕ)
    (h : address≤profile model (width model k Qv B Hc Hr a weights Bc Br) k Qv B Hc Hr a weights Bc Br) :
    binaryWordWidth address≤width model k Qv B Hc Hr a weights Bc Br :=
  binaryWordWidth_le_of_lt_pow (positive_width model k Qv B Hc Hr a weights Bc Br)
    (h.trans_lt (capacity model k Qv B Hc Hr a weights Bc Br))

theorem source_bound {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    GeneralPaperSourceLifetimeStorage.window model (width model k Qv B Hc Hr a weights Bc Br) k Qv a c hc weights Bc Br count<
      2^width model k Qv B Hc Hr a weights Bc Br := by
  have hs := GeneralPaperSourceLifetimeStorage.bounded model (width model k Qv B Hc Hr a weights Bc Br) k Qv a c hc weights Bc Br hw count he
  have hp := capacity model k Qv B Hc Hr a weights Bc Br
  dsimp only [profile] at hp
  omega

theorem prepared_with_first {m : ℕ} (model : RationalCostModel) (k Qv B Hc Hr : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hw : ∑ j,weights.read j=Qv)
    (hB : RationalHeight b B) (hBc : RationalHeight Bc Hc) (hBr : RationalHeight Br Hr) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    let W := width model k Qv B Hc Hr a weights Bc Br
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperPrecallResidentStorage.inputs W m k Qv b Bc Br+
      ((GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br 0 0)+64*W)+
        GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count)+
      GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2<2^W := by
  let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
  let a := ready.1.1.1.2
  let W := width model k Qv B Hc Hr a weights Bc Br
  have hs := GeneralPaperPreparedSourceLifetimeStorage.with_literal_inputs model W k Qv B Hc Hr b hb weights Bc Br hw hB hBc hBr count he
  have hf := GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _)
  have hp := capacity model k Qv B Hc Hr a weights Bc Br
  dsimp only [W,a,ready,GeneralPaperCatalogueShared.prepare] at hs hf hp ⊢
  dsimp only [profile] at hp
  omega

end Blotto.GeneralPaperPreparedReferenceCapacity
