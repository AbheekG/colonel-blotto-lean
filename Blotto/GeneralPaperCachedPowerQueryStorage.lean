import Blotto.GeneralPaperPowerConstructionStorage
import Blotto.GeneralPaperEpochPrefixConstructionStorage

/-! Storage of one query on the retained power table. All native prefixState
accumulators are reserved together, with pending suffix-work metadata and
structural frames. Primitive scratch uses the complete native bit price.
The prefixState catalogue is erased and never executes a second query. -/
namespace Blotto.GeneralPaperCachedPowerQueryStorage
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedPreparedPowers
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem scan_basic (unit p : ℕ) (hu : 0<unit) (hp : unit=2^p)
    (entries : List Entry) (hn : ∀ e∈entries,Normal unit e.number) (remaining : ℕ)
    (acc : Number) (ha : Normal unit acc) :
    Normal unit (GeneralPaperRoundedPowerQuery.scan unit p entries remaining acc).number ∧
      (GeneralPaperRoundedPowerQuery.scan unit p entries remaining acc).remaining≤remaining := by
  induction entries generalizing remaining acc with
  | nil => exact ⟨ha,Nat.le_refl _⟩
  | cons entry rest ih =>
    have he := hn entry List.mem_cons_self
    have hr : ∀ e∈rest,Normal unit e.number := fun e h => hn e (List.mem_cons_of_mem _ h)
    rw [GeneralPaperRoundedPowerQuery.scan]
    split
    · have hi := ih hr (remaining-entry.degree) _
        (GeneralPaperDyadicMultiply.multiply_normal unit p hu hp acc entry.number ha he)
      exact ⟨hi.1,hi.2.trans (Nat.sub_le _ _)⟩
    · exact ih hr remaining acc ha

theorem scan_append_state (unit p : ℕ) (first rest : List Entry) (remaining : ℕ) (acc : Number) :
    let before := GeneralPaperRoundedPowerQuery.scan unit p first remaining acc
    let after := GeneralPaperRoundedPowerQuery.scan unit p rest before.remaining before.number
    (GeneralPaperRoundedPowerQuery.scan unit p (first++rest) remaining acc).number=after.number ∧
      (GeneralPaperRoundedPowerQuery.scan unit p (first++rest) remaining acc).remaining=after.remaining := by
  induction first generalizing remaining acc with
  | nil => exact ⟨rfl,rfl⟩
  | cons entry first ih =>
    simp only [List.cons_append,GeneralPaperRoundedPowerQuery.scan]
    split
    · exact ih (remaining-entry.degree) (GeneralPaperDyadicMultiply.multiply unit p acc entry.number).number
    · exact ih remaining acc

def prefixState (c : GeneralPaperMaterializedPowerCache.Cache) (exponent visited : ℕ) :
    GeneralPaperRoundedPowerQuery.Result :=
  GeneralPaperRoundedPowerQuery.scan c.powers.format.unit c.powers.format.fractionalBits
    (c.powers.table.take visited) exponent (one c.powers.format.unit c.powers.format.fractionalBits)

def pendingCap (c : GeneralPaperMaterializedPowerCache.Cache) : ℕ :=
  GeneralPaperPowerTableBounds.metadataCap c.powers.format.fractionalBits c.powers.format.columns

def resultBits (W : ℕ) (result : GeneralPaperRoundedPowerQuery.Result) : ℕ :=
  GeneralPaperStoredNumberBits.bits result.number+fields W [result.remaining,result.work]+64*W

theorem prefix_bound (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent visited : ℕ)
    (he : exponent≤c.controls.precision.levelBound) :
    resultBits W (prefixState c exponent visited)≤3*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+98*W := by
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let prepared := GeneralPaperPreparedPowers.prepare lambda k
  have hu := GeneralPaperPowerPrecision.unit_positive lambda k
  have hp := GeneralPaperPowerPrecision.unit_power lambda k
  have hb := GeneralPaperPreparedPowers.prepared_base lambda k
  have ht := (build_good f.unit f.fractionalBits hu hp prepared.base hb.1 hb.2.1 f.columns).2
  have hn := (scan_basic f.unit f.fractionalBits (Nat.zero_lt_of_lt hu) hp (prepared.table.take visited)
    (fun e h => (ht e (List.mem_of_mem_take h)).2.1) exponent _
    (one_normal f.unit f.fractionalBits (Nat.zero_lt_of_lt hu))).1
  have hrem := (scan_basic f.unit f.fractionalBits (Nat.zero_lt_of_lt hu) hp (prepared.table.take visited)
    (fun e h => (ht e (List.mem_of_mem_take h)).2.1) exponent _
    (one_normal f.unit f.fractionalBits (Nat.zero_lt_of_lt hu))).2
  have hex := GeneralPaperPowerQueryExponent.query_prefix lambda k exponent visited
  have hnumber := GeneralPaperStoredNumberBits.operand m lambda k Qv _ hn
    (hex.trans (show exponent+f.fractionalBits≤GeneralPaperQuantileExponentRange.cap lambda k by
      change exponent≤GeneralPaperPowerPrecision.levelBound lambda k at he
      unfold GeneralPaperQuantileExponentRange.cap
      dsimp only [f]
      omega))
  have hlen : (prepared.table.take visited).length≤f.columns := by
    have h : prepared.table.length=f.columns := entries_length _ _ _ _
    simp only [List.length_take]
    omega
  have hw := GeneralPaperRoundedPowerQuery.scan_work f.unit f.fractionalBits (prepared.table.take visited) exponent
    (one f.unit f.fractionalBits)
  have hwcap : (GeneralPaperRoundedPowerQuery.scan f.unit f.fractionalBits (prepared.table.take visited) exponent
      (one f.unit f.fractionalBits)).work≤GeneralPaperPowerTableBounds.metadataCap f.fractionalBits f.columns := by
    unfold GeneralPaperPowerTableBounds.metadataCap
    nlinarith only [hw,Nat.mul_le_mul_right (12*(f.fractionalBits+1)+82) hlen]
  have hmeta := (Nat.add_le_add_left (binaryWordWidth_mono hwcap) 1).trans
    ((GeneralPaperPowerQueryBounds.metadata_word f.fractionalBits f.columns (2^f.columns)
      (GeneralPaperCachedPowerQuery.budget prepared)).trans (GeneralPaperPowerQueryEnvelope.width_bound m lambda k Qv))
  have hrword := (Nat.add_le_add_left (binaryWordWidth_mono (hrem.trans he)) 1).trans
    (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  have hf := fields_bound W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)
    [(prefixState (GeneralPaperMaterializedPowerCache.specification m lambda k Qv) exponent visited).remaining,
      (prefixState (GeneralPaperMaterializedPowerCache.specification m lambda k Qv) exponent visited).work] (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact hrword
        · exact hmeta)
  change _≤2*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W at hf
  have hnumber' : GeneralPaperStoredNumberBits.bits
      (prefixState (GeneralPaperMaterializedPowerCache.specification m lambda k Qv) exponent visited).number≤
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := hnumber
  dsimp only [resultBits]
  omega

def frame (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) (exponent visited : ℕ) : ℕ :=
  resultBits W (prefixState c exponent visited)+fields W [pendingCap c,visited]+256*W

def frames (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) : ℕ :=
  ∑ visited∈Finset.range (c.powers.format.columns+1),frame W c exponent visited

theorem frames_bound (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ)
    (he : exponent≤c.controls.precision.levelBound) : frames W c exponent≤
      ((GeneralPaperPowerPrecision.prepare lambda k).columns+1)*
        (5*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+388*W) := by
  have hmeta : natBits (pendingCap c)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hc]
    exact (GeneralPaperPowerQueryBounds.metadata_word _ _ _ _).trans
      (GeneralPaperPowerQueryEnvelope.width_bound m lambda k Qv)
  have hcols : natBits c.powers.format.columns≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
    have hm := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).columns
    have hw := GeneralPaperInitializerControlCounters.word_le_self (GeneralPaperPowerPrecision.prepare lambda k).columns
    rw [hc]
    dsimp only [GeneralPaperMaterializedPowerCache.specification,GeneralPaperPreparedPowers.prepare]
    unfold natBits GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  have hframe (visited : ℕ) (hv : visited∈Finset.range (c.powers.format.columns+1)) :
      frame W c exponent visited≤5*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+388*W := by
    have hp := prefix_bound W m lambda k Qv c hc exponent visited he
    have hvisit := (Nat.add_le_add_left (binaryWordWidth_mono (show visited≤c.powers.format.columns by
      have h := Finset.mem_range.mp hv
      omega)) 1).trans hcols
    have hf := fields_bound W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)
      [pendingCap c,visited] (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact hmeta
        · exact hvisit)
    change _≤2*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W at hf
    dsimp only [frame]
    omega
  have hs := Finset.sum_le_sum hframe
  have hfmt : c.powers.format.columns=(GeneralPaperPowerPrecision.prepare lambda k).columns := by rw [hc]; rfl
  simpa only [frames,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,hfmt] using hs

def window (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) : ℕ :=
  frames W c exponent+resultBits W (GeneralPaperCachedPowerQuery.query model.rat W c exponent).1+
    formatFootprint W c.powers.format+(GeneralPaperCachedPowerQuery.query model.rat W c exponent).2+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  ((GeneralPaperPowerPrecision.prepare lambda k).columns+1)*(5*H+388*W)+
    (3*H+98*W)+(4*(H+W)+32*W)+
    131072*GeneralPaperSourcePreparationSizes.measure m lambda k Qv*(W+model.rat H)+256*W

theorem returned_bound (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ)
    (he : exponent≤c.controls.precision.levelBound) :
    resultBits W (GeneralPaperCachedPowerQuery.query model.rat W c exponent).1≤
      3*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+98*W := by
  let out := (GeneralPaperCachedPowerQuery.query model.rat W c exponent).1
  have cert := GeneralPaperCachedPowerQuery.approximation model.rat W m lambda k Qv c hc exponent he
  have hn : Normal (GeneralPaperPowerPrecision.prepare lambda k).unit out.number := by
    have h := cert.2.1
    have hu : c.controls.precision.parameters.unit=(GeneralPaperPowerPrecision.prepare lambda k).unit := by rw [hc]; rfl
    rw [hu] at h
    exact h
  have hex := GeneralPaperPowerQueryExponent.cached model.rat W m lambda k Qv c hc exponent he
  have he' : out.number.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k := by
    apply hex.trans
    rw [hc]
    unfold GeneralPaperQuantileExponentRange.cap
    change GeneralPaperPowerPrecision.levelBound lambda k+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits≤_
    omega
  have hnumber := GeneralPaperStoredNumberBits.operand m lambda k Qv out.number hn he'
  have hwork : out.work≤GeneralPaperPowerTableBounds.metadataCap
      (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits (GeneralPaperPowerPrecision.prepare lambda k).columns := by
    dsimp only [out]
    rw [GeneralPaperCachedPowerQuery.data model.rat W m lambda k Qv c hc exponent,hc]
    have h := GeneralPaperRoundedPowerQuery.evaluate_work
      (GeneralPaperPowerPrecision.prepare lambda k).unit (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
      (GeneralPaperPowerPrecision.prepare lambda k).columns exponent (GeneralPaperPreparedPowers.prepare lambda k).base
    change (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) exponent).work≤_ at h ⊢
    unfold GeneralPaperPowerTableBounds.metadataCap
    nlinarith only [h]
  have hmeta := (Nat.add_le_add_left (binaryWordWidth_mono hwork) 1).trans
    ((GeneralPaperPowerQueryBounds.metadata_word _ _ _ _).trans (GeneralPaperPowerQueryEnvelope.width_bound m lambda k Qv))
  have hzero : natBits out.remaining≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have h := cert.1
    change out.remaining=0 at h
    rw [h]
    have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
    have hz : natBits 0=2 := by decide
    rw [hz]
    unfold GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  have hf := fields_bound W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)
    [out.remaining,out.work] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact hzero
      · exact hmeta)
  change _≤2*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W at hf
  change GeneralPaperStoredNumberBits.bits out.number+fields W [out.remaining,out.work]+64*W≤_
  omega

theorem bounded (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ)
    (he : exponent≤c.controls.precision.levelBound) : window model W c exponent≤profile model W m lambda k Qv := by
  have hf := frames_bound W m lambda k Qv c hc exponent he
  have hr := returned_bound model W m lambda k Qv c hc exponent he
  have hs := GeneralPaperPowerQueryEnvelope.work model.rat model.monotone W m lambda k Qv c hc exponent he
  have hfmt : formatFootprint W c.powers.format≤
      4*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
    rw [hc]
    exact format_bound W m lambda k Qv
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperCachedPowerQueryStorage
