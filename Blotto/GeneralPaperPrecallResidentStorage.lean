import Blotto.GeneralPaperClassifierConstructionStorage
import Blotto.GeneralPaperPreparationResidentStorage

/-! The actual front is retained throughout materialization and source
execution. Join it to the complete source cache, epoch residents and first
trajectory. Literal classifier/source budget scales keep their own heights;
the original-input/compiler height calibration and global W remain separate. -/
namespace Blotto.GeneralPaperPrecallResidentStorage
open GeneralPaperEncodedScalarStorage GeneralPaperClassifierResultStorage
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def sourcePrecallProfile (W m k Qv : ℕ) : ℕ :=
  frontProfile W m k+GeneralPaperPreparationCacheStorage.profile W m
    (GeneralPaperProxyParameters.alphabet m k).lambda k Qv+64*W

theorem source_precall (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    let r := (GeneralPaperSourcePrecallPreparation.prepare model W m k Qv b).1
    frontFootprint W r.1+GeneralPaperPreparationCacheStorage.footprint W r.2+64*W≤
      sourcePrecallProfile W m k Qv := by
  dsimp only
  rw [GeneralPaperSourcePrecallPreparation.data]
  have hr := front_native W m k (b:ℝ) (by exact_mod_cast hb)
  have hs := GeneralPaperPreparationCacheStorage.native W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv
  unfold sourcePrecallProfile
  dsimp only
  omega

def inputs (W m k Qv : ℕ) (b Bc Br : ℚ) : ℕ :=
  rationalWordWidth b+rationalWordWidth Bc+rationalWordWidth Br+fields W [m,k,Qv]+64*W

def inputProfile (W m k Qv B Hc Hr : ℕ) : ℕ :=
  (1+2*B)+(1+2*Hc)+(1+2*Hr)+natBits m+natBits k+natBits Qv+99*W

theorem input_scales (W m k Qv B Hc Hr : ℕ) (b Bc Br : ℚ)
    (hb : RationalHeight b B) (hc : RationalHeight Bc Hc) (hr : RationalHeight Br Hr) :
    inputs W m k Qv b Bc Br≤ inputProfile W m k Qv B Hc Hr := by
  have h0 := rationalWordWidth_of_height hb
  have h1 := rationalWordWidth_of_height hc
  have h2 := rationalWordWidth_of_height hr
  unfold inputs inputProfile fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

theorem prepared_front {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    frontFootprint W (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1.1.1≤frontProfile W m k := by
  rw [GeneralPaperPreparedSharedSource.data]
  apply front_native W m k (b:ℝ)
  exact_mod_cast hb

def residentProfile {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  frontProfile W m k+GeneralPaperPreparationResidentStorage.residentProfile W k Qv a weights Bc Br+64*W

theorem prepared_resident {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv r.1.1.1.2 weights Bc Br epoch time)+64*W≤
      residentProfile W k Qv r.1.1.1.2 weights Bc Br := by
  have hf := prepared_front model W k Qv b hb weights Bc Br
  have hs := GeneralPaperPreparationResidentStorage.prepared_resident model W k Qv b weights Bc Br epoch time he ht
  exact Nat.add_le_add_right (Nat.add_le_add hf hs) _

theorem with_inputs {m : ℕ} (model : RationalCostModel) (W k Qv B Hc Hr : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hB : RationalHeight b B)
    (hBc : RationalHeight Bc Hc) (hBr : RationalHeight Br Hr) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    inputs W m k Qv b Bc Br+
      (frontFootprint W r.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv r.1.1.1.2 weights Bc Br epoch time)+64*W)≤
      inputProfile W m k Qv B Hc Hr+residentProfile W k Qv r.1.1.1.2 weights Bc Br :=
  Nat.add_le_add (input_scales W m k Qv B Hc Hr b Bc Br hB hBc hBr)
    (prepared_resident model W k Qv b hb weights Bc Br epoch time he ht)

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let first := GeneralPaperCatalogueShared.prepare a k Qv weights firstBc firstBr
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
      (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
        (frontFootprint W r.1.1+
          (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
            GeneralPaperEpochResidentStorage.footprint W k Qv r.1.1.1.2 weights Bc Br epoch time)+64*W)≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+residentProfile W k Qv a weights Bc Br := by
  dsimp only
  have hf := GeneralPaperEncodedTrajectoryStorage.actual W k Qv (GeneralPaperProxyParameters.alphabet m k)
    weights firstBc firstBr _ (Nat.le_refl _)
  have hs := prepared_resident model W k Qv b hb weights Bc Br epoch time he ht
  rw [GeneralPaperPreparedSharedSource.data] at hs ⊢
  exact Nat.add_le_add hf hs

end Blotto.GeneralPaperPrecallResidentStorage
