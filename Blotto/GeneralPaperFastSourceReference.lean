import Blotto.GeneralPaperSourceSpaceMonotonicity

/-! A single reference width derived from the explicit fast storage majorant
works for every actual primitive model under the same Growth condition.
Native time, retained inputs/front/cache and first-trajectory lifetime bounds
share that width. No primitive implementation is substituted in an execution,
and no space/word oracle or runtime census is used. Final soft-O bounds remain
separate from this closed-profile reference/capacity calibration. -/
namespace Blotto.GeneralPaperFastSourceReference
open GeneralPaperFastRationalModel GeneralPaperCodeAlphabet
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def profile {m : ℕ} (C d W k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperPreparedReferenceCapacity.profile (GeneralPaperFastRationalMajorant.model C d) W k Qv B Hc Hr a weights Bc Br

def width {m : ℕ} (C d k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperPreparedReferenceCapacity.width (GeneralPaperFastRationalMajorant.model C d) k Qv B Hc Hr a weights Bc Br

theorem positive {m : ℕ} (C d k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : 1≤width C d k Qv B Hc Hr a weights Bc Br :=
  GeneralPaperPreparedReferenceCapacity.positive_width _ k Qv B Hc Hr a weights Bc Br

theorem control_word {m : ℕ} (C d k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperPrecallControlWord.word m k≤width C d k Qv B Hc Hr a weights Bc Br :=
  GeneralPaperPreparedReferenceCapacity.control_word _ k Qv B Hc Hr a weights Bc Br

theorem dominates {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W k Qv B Hc Hr : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperPreparedReferenceCapacity.profile actual W k Qv B Hc Hr a weights Bc Br≤profile C d W k Qv B Hc Hr a weights Bc Br :=
  GeneralPaperSourceSpaceMonotonicity.prepared actual _ (GeneralPaperFastRationalMajorant.dominates hg) W k Qv B Hc Hr a weights Bc Br

theorem capacity {m : ℕ} (C d k Qv B Hc Hr : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    profile C d (width C d k Qv B Hc Hr a weights Bc Br) k Qv B Hc Hr a weights Bc Br<
      2^width C d k Qv B Hc Hr a weights Bc Br :=
  GeneralPaperPreparedReferenceCapacity.capacity _ k Qv B Hc Hr a weights Bc Br

theorem actual_capacity {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (k Qv B Hc Hr : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperPreparedReferenceCapacity.profile actual (width C d k Qv B Hc Hr a weights Bc Br) k Qv B Hc Hr a weights Bc Br<
      2^width C d k Qv B Hc Hr a weights Bc Br :=
  (dominates hg _ k Qv B Hc Hr a weights Bc Br).trans_lt (capacity C d k Qv B Hc Hr a weights Bc Br)

theorem actual_address {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (k Qv B Hc Hr : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (address : ℕ)
    (ha : address≤GeneralPaperPreparedReferenceCapacity.profile actual (width C d k Qv B Hc Hr a weights Bc Br) k Qv B Hc Hr a weights Bc Br) :
    binaryWordWidth address≤width C d k Qv B Hc Hr a weights Bc Br :=
  binaryWordWidth_le_of_lt_pow (positive C d k Qv B Hc Hr a weights Bc Br)
    (ha.trans_lt (actual_capacity hg k Qv B Hc Hr a weights Bc Br))

theorem source_time_and_space {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (k Qv B Hc Hr : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    let W := width C d k Qv B Hc Hr a weights Bc Br
    let shared := prepare a k Qv weights Bc Br
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) actual W k Qv a c hc shared count).2≤
      GeneralPaperFastSourceMajorant.profile C d W m k Qv a count ∧
    GeneralPaperSourceLifetimeStorage.window actual W k Qv a c hc weights Bc Br count<2^W := by
  refine ⟨GeneralPaperFastSourceMajorant.native_work hg _ k Qv a c hc weights Bc Br hw count he hbc hbr,?_⟩
  have hs := GeneralPaperSourceLifetimeStorage.bounded actual (width C d k Qv B Hc Hr a weights Bc Br) k Qv a c hc weights Bc Br hw count he
  have hp := actual_capacity hg k Qv B Hc Hr a weights Bc Br
  dsimp only [GeneralPaperPreparedReferenceCapacity.profile] at hp
  omega

theorem prepared_live_bound {m : ℕ} (actual : RationalCostModel) (W k Qv B Hc Hr : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hw : ∑ j,weights.read j=Qv)
    (hB : RationalHeight b B) (hBc : RationalHeight Bc Hc) (hBr : RationalHeight Br Hr) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let ready := (GeneralPaperPreparedSharedSource.prepare actual k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperPrecallResidentStorage.inputs W m k Qv b Bc Br+
      ((GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br 0 0)+64*W)+
        GeneralPaperSourceLifetimeStorage.window actual W k Qv a c hc weights Bc Br count)+
      GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2≤
        GeneralPaperPreparedReferenceCapacity.profile actual W k Qv B Hc Hr a weights Bc Br := by
  let ready := (GeneralPaperPreparedSharedSource.prepare actual k Qv b weights Bc Br).1
  let a := ready.1.1.1.2
  have hs := GeneralPaperPreparedSourceLifetimeStorage.with_literal_inputs actual W k Qv B Hc Hr b hb weights Bc Br hw hB hBc hBr count he
  have hf := GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _)
  dsimp only [a,ready,GeneralPaperCatalogueShared.prepare] at hs hf ⊢
  dsimp only [GeneralPaperPreparedReferenceCapacity.profile]
  omega

def preparedWidth {m : ℕ} (C d k Qv B Hc Hr : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  width C d k Qv B Hc Hr (GeneralPaperProxyParameters.alphabet m k) weights Bc Br

theorem prepared_width_log_bound {m : ℕ} (C d k Qv B Hc Hr : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    preparedWidth C d k Qv B Hc Hr weights Bc Br≤
      4*binaryWordWidth (profile C d 1 k Qv B Hc Hr (GeneralPaperProxyParameters.alphabet m k) weights Bc Br)+
        192+8*binaryWordWidth (k+1)+8*binaryWordWidth ((GeneralPaperProxyParameters.alphabet m k).lambda+1) := by
  have hw := GeneralPaperPrecallWordEnvelope.word_bound m k
  dsimp only [preparedWidth,width,profile,GeneralPaperPreparedReferenceCapacity.width,GeneralPaperReferenceCapacity.referenceWord]
  omega

theorem prepared_live_capacity {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (k Qv B Hc Hr : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hw : ∑ j,weights.read j=Qv)
    (hB : RationalHeight b B) (hBc : RationalHeight Bc Hc) (hBr : RationalHeight Br Hr) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let W := preparedWidth C d k Qv B Hc Hr weights Bc Br
    let ready := (GeneralPaperPreparedSharedSource.prepare actual k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperPrecallResidentStorage.inputs W m k Qv b Bc Br+
      ((GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br 0 0)+64*W)+
        GeneralPaperSourceLifetimeStorage.window actual W k Qv a c hc weights Bc Br count)+
      GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2<2^W := by
  let ready := (GeneralPaperPreparedSharedSource.prepare actual k Qv b weights Bc Br).1
  let a := ready.1.1.1.2
  let W := preparedWidth C d k Qv B Hc Hr weights Bc Br
  have ha : a=GeneralPaperProxyParameters.alphabet m k := by dsimp only [a,ready]; rw [GeneralPaperPreparedSharedSource.data]
  have hl := prepared_live_bound actual W k Qv B Hc Hr b hb weights Bc Br firstBc firstBr hw hB hBc hBr count he
  have hm := dominates hg W k Qv B Hc Hr a weights Bc Br
  have heq : profile C d W k Qv B Hc Hr a weights Bc Br=
      profile C d W k Qv B Hc Hr (GeneralPaperProxyParameters.alphabet m k) weights Bc Br := by rw [ha]
  exact hl.trans_lt ((hm.trans_eq heq).trans_lt (capacity C d k Qv B Hc Hr _ weights Bc Br))

end Blotto.GeneralPaperFastSourceReference
