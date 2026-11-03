import Blotto.GeneralPaperCachedPowerQueryStorage

/-! Native numerator fills retain both reserved prefixes, the full array,
structural frames, and one guarded cached-power/conversion callback. Local
raw conversion fields use the derived short source word, not alphabet codes.
No previous numerator array or table is reconstructed by this observer. -/
namespace Blotto.GeneralPaperEpochNumeratorConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def callback {n : ℕ} (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (levels : FixedArrayTable n ℕ) : Fin n → ℕ × ℕ :=
  GeneralPaperEpochNumeratorArrayPrice.element true model.rat W c levels

theorem values {n : ℕ} (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (levels : FixedArrayTable n ℕ)
    (hl : ∀ r,levels.read r≤c.controls.precision.levelBound) (r : Fin n) :
    (callback model W c levels r).1≤4*(GeneralPaperPowerPrecision.prepare lambda k).unit := by
  rw [callback,GeneralPaperEpochNumeratorArrayPrice.element_data true model.rat W m lambda k Qv c hc]
  have hn : Normal c.powers.format.unit (GeneralPaperPreparedPowers.query c.powers (levels.read r)).number := by
    rw [hc]
    have h := hl r
    rw [hc] at h
    exact (GeneralPaperPreparedPowers.query_certificate lambda k _ h).2.1
  have hb := GeneralPaperLocalNumeratorPrice.bound c.powers.format.unit c.powers.format.fractionalBits _ hn
  have hu : c.powers.format.unit=(GeneralPaperPowerPrecision.prepare lambda k).unit := by rw [hc]; rfl
  rwa [hu] at hb

def elementWindow {n : ℕ} (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (levels : FixedArrayTable n ℕ) (r : Fin n) : ℕ :=
  let x := (GeneralPaperCachedPowerQuery.query model.rat W c (levels.read r)).1.number
  GeneralPaperCachedPowerQueryStorage.window model W c (levels.read r)+
    fields W [c.powers.format.unit,c.powers.format.fractionalBits,levels.read r,x.mantissa,2*x.mantissa,
      (callback model W c levels r).1,x.exponent.natAbs,r.val,n]+
    (callback model W c levels r).2+256*W

def elementProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  GeneralPaperCachedPowerQueryStorage.profile model W m lambda k Qv+
    9*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+natBits (n+1)+W)+32*W+
    GeneralPaperEpochNumeratorArrayPrice.elementProfile model.rat W m lambda k Qv+256*W

theorem element_bound {n : ℕ} (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (levels : FixedArrayTable n ℕ)
    (hl : ∀ r,levels.read r≤c.controls.precision.levelBound) (r : Fin n) :
    elementWindow model W c levels r≤elementProfile model W m lambda k Qv n := by
  let x := (GeneralPaperCachedPowerQuery.query model.rat W c (levels.read r)).1.number
  have hq := GeneralPaperCachedPowerQueryStorage.bounded model W m lambda k Qv c hc _ (hl r)
  have cert := GeneralPaperCachedPowerQuery.approximation model.rat W m lambda k Qv c hc _ (hl r)
  have hn : Normal c.powers.format.unit x := by
    have hu : c.controls.precision.parameters.unit=c.powers.format.unit := by rw [hc]; rfl
    have h := cert.2.1
    rw [hu] at h
    exact h
  have hm : x.mantissa≤2*c.powers.format.unit := by rcases hn with h|h <;> omega
  have he := GeneralPaperPowerQueryExponent.cached model.rat W m lambda k Qv c hc _ (hl r)
  have hex : x.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k := by
    apply he.trans
    rw [hc]
    unfold GeneralPaperQuantileExponentRange.cap
    change GeneralPaperPowerPrecision.levelBound lambda k+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits≤_
    omega
  have hw : GeneralPaperLocalNumeratorPrice.width c.powers.format.unit c.powers.format.fractionalBits x≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have h := GeneralPaperLocalNumeratorPrice.operand_width m lambda k Qv x hex
    have hu : c.powers.format.unit=(GeneralPaperPowerPrecision.prepare lambda k).unit := by rw [hc]; rfl
    have hp : c.powers.format.fractionalBits=(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits := by rw [hc]; rfl
    rwa [hu,hp]
  have hraw := (GeneralPaperLocalNumeratorPrice.natural_word c.powers.format.unit c.powers.format.fractionalBits x).trans hw
  have hv := values model W m lambda k Qv c hc levels hl r
  have hv' : (callback model W c levels r).1≤4*c.powers.format.unit := by
    have hu : c.powers.format.unit=(GeneralPaperPowerPrecision.prepare lambda k).unit := by rw [hc]; rfl
    rwa [hu]
  have hunit : natBits c.powers.format.unit≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    unfold natBits GeneralPaperLocalNumeratorPrice.width at *
    omega
  have hp : natBits c.powers.format.fractionalBits≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    unfold natBits GeneralPaperLocalNumeratorPrice.width at *
    omega
  have hx : natBits x.exponent.natAbs≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    unfold natBits GeneralPaperLocalNumeratorPrice.width at *
    omega
  have hlevel : natBits (levels.read r)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have h := hl r
    have hg : c.controls.precision.levelBound=GeneralPaperPowerPrecision.levelBound lambda k := by rw [hc]; rfl
    rw [hg] at h
    exact (Nat.add_le_add_left (binaryWordWidth_mono h) 1).trans (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  have hf := fields_bound W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+natBits (n+1))
    [c.powers.format.unit,c.powers.format.fractionalBits,levels.read r,x.mantissa,2*x.mantissa,
      (callback model W c levels r).1,x.exponent.natAbs,r.val,n] (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with ha|ha|ha|ha|ha|ha|ha|ha|ha <;> rw [ha]
      · omega
      · omega
      · omega
      · have h := (Nat.add_le_add_left (binaryWordWidth_mono (show x.mantissa≤4*c.powers.format.unit+2 by omega)) 1).trans hraw
        change natBits _≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv at h
        omega
      · have h := (Nat.add_le_add_left (binaryWordWidth_mono (show 2*x.mantissa≤4*c.powers.format.unit+2 by omega)) 1).trans hraw
        change natBits _≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv at h
        omega
      · have h := (Nat.add_le_add_left (binaryWordWidth_mono (show (callback model W c levels r).1≤4*c.powers.format.unit+2 by omega)) 1).trans hraw
        change natBits _≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv at h
        omega
      · omega
      · have h := Nat.add_le_add_left (binaryWordWidth_mono (show r.val≤n+1 by omega)) 1
        change natBits r.val≤natBits (n+1) at h
        omega
      · have h := Nat.add_le_add_left (binaryWordWidth_mono (show n≤n+1 by omega)) 1
        change natBits n≤natBits (n+1) at h
        omega)
  change _≤9*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+natBits (n+1)+W)+32*W at hf
  have hs := GeneralPaperEpochNumeratorArrayPrice.element_bit_work model.rat model.monotone W m lambda k Qv c hc levels r (hl r)
  change (callback model W c levels r).2≤_ at hs
  dsimp only [elementWindow,elementProfile]
  dsimp only [x] at hf
  omega

def active {n : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (levels : FixedArrayTable n ℕ) (count : ℕ) : ℕ :=
  if h : count<n then elementWindow model W c levels ⟨count,h⟩ else 0

theorem active_finished {n : ℕ} (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (levels : FixedArrayTable n ℕ) (count : ℕ) (hc : n≤count) :
    active model W c levels count=0 := by
  simp only [active,dite_eq_right (Nat.not_lt.mpr hc)]

def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (levels : FixedArrayTable n ℕ) (count : ℕ) (ht : count≤n) : ℕ :=
  GeneralPaperNativeNatFillStorage.window W (callback model W c levels) count ht+
    active model W c levels count+256*W

def profile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  2*(n*(H+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W n+
    (n*(H+W)+32*W)+H+4*(natBits (n+1)+W)+160*W+
    elementProfile model W m lambda k Qv n+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (levels : FixedArrayTable n ℕ)
    (hl : ∀ r,levels.read r≤c.controls.precision.levelBound) (count : ℕ) (ht : count≤n) :
    window model W c levels count ht≤profile model W m lambda k Qv n := by
  have hf := GeneralPaperNativeNatFillStorage.bounded W (4*(GeneralPaperPowerPrecision.prepare lambda k).unit)
    (callback model W c levels) (values model W m lambda k Qv c hc levels hl) count ht
  have hw := GeneralPaperEncodedSnapshotStorage.numerator_word m lambda k Qv
    (4*(GeneralPaperPowerPrecision.prepare lambda k).unit) (Nat.le_refl _)
  change natBits (4*(GeneralPaperPowerPrecision.prepare lambda k).unit)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv at hw
  have ha : active model W c levels count≤elementProfile model W m lambda k Qv n := by
    unfold active
    split
    · exact element_bound model W m lambda k Qv c hc levels hl _
    · exact Nat.zero_le _
  have hmono : GeneralPaperNativeNatFillStorage.profile W n (4*(GeneralPaperPowerPrecision.prepare lambda k).unit)≤
      2*(n*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+64*W)+
      GeneralPaperGridArrayConstructionStorage.frames W n+
      (n*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W)+
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+4*(natBits (n+1)+W)+160*W := by
    unfold GeneralPaperNativeNatFillStorage.profile
    gcongr
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEpochNumeratorConstructionStorage
