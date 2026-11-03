import Blotto.FareyCeiling
import Blotto.FareyRankRepresentation

/-! Actual R127 direct rank-universe cuts. Each of the closed/shifted sources
uses one exact Farey ceiling, then the smaller allowed distinguished code is
returned. No decoder binary search or code enumeration is performed. Weak and
strict threshold equality, duplicate decoded labels and signed empty caps are
retained. Quotient callbacks are counted separately from complete bit prices. -/

namespace Blotto.Farey

def translatedBid (spec : RankUniverse) (shifted : Bool) (bid : Fraction) : ℚ :=
  bid.value + if shifted then spec.shift else 0

def distinguishedCode (spec : RankUniverse) (shifted : Bool) (bid : Fraction) : ℕ :=
  closedCode spec.order bid + if shifted then 1 else 0

def AllowedBid (spec : RankUniverse) (shifted : Bool) (bid : Fraction) : Prop :=
  bid.den ≤ spec.order ∧ translatedBid spec shifted bid ≤ 1 ∧ (if shifted then 0 < spec.shift else True)

structure CutCandidate (spec : RankUniverse) (strict shifted : Bool) (threshold : ℚ) where
  code : ℕ
  quotientQueries : ℕ
  bound : code ≤ rankCap spec.order + 1
  queries_bound : quotientQueries ≤ 6 * binaryWordWidth spec.order + 1
  sound : code ≤ rankCap spec.order → Above strict threshold (spec.decode code)
  complete : ∀ bid : Fraction, AllowedBid spec shifted bid → Above strict threshold (translatedBid spec shifted bid) →
    code ≤ distinguishedCode spec shifted bid

theorem closedCode_mono (D : ℕ) (first second : Fraction) (h : first.value ≤ second.value) :
    closedCode D first ≤ closedCode D second := by
  unfold closedCode
  apply Nat.mul_le_mul_left
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

def closedCandidate (spec : RankUniverse) (strict : Bool) (threshold : ℚ) : CutCandidate spec strict false threshold :=
  let nearest := ceiling spec.order spec.order_positive strict threshold
  match h : nearest.1 with
  | none =>
    { code := rankCap spec.order + 1
      quotientQueries := nearest.2
      bound := le_rfl
      queries_bound := (ceiling_queries spec.order spec.order_positive strict threshold).trans (by omega)
      sound := by intro hc; omega
      complete := by
        intro bid hb ha
        have hn := (ceiling_none spec.order spec.order_positive strict threshold).mp h
        have hu : bid.value ≤ 1 := by simpa [AllowedBid, translatedBid] using hb.2.1
        have hp : Above strict threshold bid.value := by simpa [translatedBid] using ha
        exact False.elim (hn (above_mono strict threshold bid.value 1 hu hp)) }
  | some endpoint =>
    { code := closedCode spec.order endpoint.fraction
      quotientQueries := nearest.2 + 1
      bound := (closedCode_le_rankCap spec.order spec.order_positive endpoint.fraction endpoint.unit).trans (by omega)
      queries_bound := Nat.add_le_add_right (ceiling_queries spec.order spec.order_positive strict threshold) 1
      sound := by
        intro _
        rw [decode_closed_bid spec endpoint.fraction endpoint.bounded endpoint.unit]
        exact endpoint.above
      complete := by
        intro bid hb ha
        have hp : Above strict threshold bid.value := by simpa [translatedBid] using ha
        have hv := endpoint.least bid hb.1 hp
        simpa [distinguishedCode] using closedCode_mono spec.order endpoint.fraction bid hv }

def shiftedCandidate (spec : RankUniverse) (strict : Bool) (threshold : ℚ) : CutCandidate spec strict true threshold :=
  if hShift : 0 < spec.shift then
    let nearest := ceiling spec.order spec.order_positive strict (threshold - spec.shift)
    match h : nearest.1 with
    | none =>
      { code := rankCap spec.order + 1
        quotientQueries := nearest.2
        bound := le_rfl
        queries_bound := (ceiling_queries spec.order spec.order_positive strict (threshold - spec.shift)).trans (by omega)
        sound := by intro hc; omega
        complete := by
          intro bid hb ha
          have hn := (ceiling_none spec.order spec.order_positive strict (threshold - spec.shift)).mp h
          have hp : Above strict (threshold - spec.shift) bid.value := (above_translate strict threshold bid.value spec.shift).mp ha
          have hu : bid.value ≤ 1 := by
            have hUnit : bid.value + spec.shift ≤ 1 := hb.2.1
            linarith
          exact False.elim (hn (above_mono strict _ bid.value 1 hu hp)) }
    | some endpoint =>
      if hAllowed : endpoint.fraction.value + spec.shift ≤ 1 then
        { code := closedCode spec.order endpoint.fraction + 1
          quotientQueries := nearest.2 + 1
          bound := (shiftedCode_valid spec endpoint.fraction hShift hAllowed).le.trans (by omega)
          queries_bound := Nat.add_le_add_right (ceiling_queries spec.order spec.order_positive strict (threshold - spec.shift)) 1
          sound := by
            intro _
            rw [decode_shifted_bid spec endpoint.fraction endpoint.bounded hShift hAllowed]
            exact (above_translate strict threshold endpoint.fraction.value spec.shift).mpr endpoint.above
          complete := by
            intro bid hb ha
            have hp : Above strict (threshold - spec.shift) bid.value := (above_translate strict threshold bid.value spec.shift).mp ha
            have hv := endpoint.least bid hb.1 hp
            simpa [distinguishedCode] using Nat.add_le_add_right (closedCode_mono spec.order endpoint.fraction bid hv) 1 }
      else
        { code := rankCap spec.order + 1
          quotientQueries := nearest.2
          bound := le_rfl
          queries_bound := (ceiling_queries spec.order spec.order_positive strict (threshold - spec.shift)).trans (by omega)
          sound := by intro hc; omega
          complete := by
            intro bid hb ha
            have hp : Above strict (threshold - spec.shift) bid.value := (above_translate strict threshold bid.value spec.shift).mp ha
            have hv := endpoint.least bid hb.1 hp
            have hu : bid.value + spec.shift ≤ 1 := hb.2.1
            exact False.elim (hAllowed (by linarith)) }
  else
    { code := rankCap spec.order + 1
      quotientQueries := 0
      bound := le_rfl
      queries_bound := by omega
      sound := by intro hc; omega
      complete := by intro bid hb _; exact False.elim (hShift hb.2.2) }

theorem decode_witness (spec : RankUniverse) (code : ℕ) (hc : code ≤ rankCap spec.order) :
    ∃ shifted : Bool, ∃ bid : Fraction, AllowedBid spec shifted bid ∧ spec.decode code = translatedBid spec shifted bid ∧
      distinguishedCode spec shifted bid ≤ code := by
  by_cases hk : code < rankCap spec.order
  · let bid := spec.base code hk
    have hd := (base_bounds spec code hk).1
    have hu : bid.value ≤ 1 := (base_bounds spec code hk).2.le.trans (rankCutoff_valid _ spec.order_positive _ hk).2
    have hb : closedCode spec.order bid ≤ code := (closedCode_cutoff spec.order spec.order_positive bid code).mpr
      (base_bounds spec code hk).2
    by_cases hs : 0 < spec.shift ∧ closedCode spec.order bid + 1 ≤ code ∧ bid.value + spec.shift ≤ 1
    · refine ⟨true, bid, ⟨hd, hs.2.2, hs.1⟩, ?_, hs.2.1⟩
      change (if h : code < rankCap spec.order then spec.bump code (spec.base code h) else 1) = bid.value + spec.shift
      simp only [hk, dite_true]
      exact ite_eq_left hs
    · refine ⟨false, bid, ⟨hd, by simpa [translatedBid] using hu, trivial⟩, ?_, ?_⟩
      · change (if h : code < rankCap spec.order then spec.bump code (spec.base code h) else 1) = bid.value + 0
        simp only [hk, dite_true, add_zero]
        exact ite_eq_right hs
      · simpa [distinguishedCode] using hb
  · have he : code = rankCap spec.order := by omega
    refine ⟨false, oneFraction, ⟨by change 1 ≤ spec.order; have hp := spec.order_positive; omega,
      by norm_num [translatedBid, oneFraction, Fraction.value], trivial⟩, ?_, ?_⟩
    · rw [he, decode_terminal]
      norm_num [translatedBid, oneFraction, Fraction.value]
    · rw [he]
      simp [distinguishedCode, closedCode, oneFraction, Fraction.value, rankCap]

def directFirst (spec : RankUniverse) (strict : Bool) (threshold : ℚ) : ℕ × ℕ :=
  let closed := closedCandidate spec strict threshold
  let shifted := shiftedCandidate spec strict threshold
  (min closed.code shifted.code, closed.quotientQueries + shifted.quotientQueries)

theorem directFirst_bound (spec : RankUniverse) (strict : Bool) (threshold : ℚ) :
    (directFirst spec strict threshold).1 ≤ rankCap spec.order + 1 :=
  (min_le_left _ _).trans (closedCandidate spec strict threshold).bound

theorem directFirst_queries (spec : RankUniverse) (strict : Bool) (threshold : ℚ) :
    (directFirst spec strict threshold).2 ≤ 12 * binaryWordWidth spec.order + 2 := by
  have hc := (closedCandidate spec strict threshold).queries_bound
  have hs := (shiftedCandidate spec strict threshold).queries_bound
  unfold directFirst
  dsimp only
  omega

theorem directFirst_contract (spec : RankUniverse) (strict : Bool) (threshold : ℚ)
    (code : ℕ) (hc : code ≤ rankCap spec.order) :
    Above strict threshold (spec.decode code) ↔ (directFirst spec strict threshold).1 ≤ code := by
  constructor
  · intro ha
    rcases decode_witness spec code hc with ⟨shifted, bid, hb, he, hk⟩
    rw [he] at ha
    cases shifted
    · exact (min_le_left _ _).trans (((closedCandidate spec strict threshold).complete bid hb ha).trans hk)
    · exact (min_le_right _ _).trans (((shiftedCandidate spec strict threshold).complete bid hb ha).trans hk)
  · intro hf
    let first := closedCandidate spec strict threshold
    let second := shiftedCandidate spec strict threshold
    change min first.code second.code ≤ code at hf
    by_cases h : first.code ≤ second.code
    · rw [min_eq_left h] at hf
      have hs := first.sound (hf.trans hc)
      exact above_mono strict threshold _ _ (decode_mono spec _ _ hf hc) hs
    · rw [min_eq_right (le_of_not_ge h)] at hf
      have hs := second.sound (hf.trans hc)
      exact above_mono strict threshold _ _ (decode_mono spec _ _ hf hc) hs

def RankUniverse.directWeak (spec : RankUniverse) (threshold : ℚ) : ℕ × ℕ := directFirst spec false threshold
def RankUniverse.directStrict (spec : RankUniverse) (threshold : ℚ) : ℕ × ℕ := directFirst spec true threshold
def RankUniverse.directCap (spec : RankUniverse) (budget : ℚ) : ℤ := (spec.directStrict budget).1 - (1 : ℤ)

theorem directCap_exact (spec : RankUniverse) (budget : ℚ) (code : ℕ) (hc : code ≤ rankCap spec.order) :
    spec.decode code ≤ budget ↔ (code : ℤ) ≤ spec.directCap budget := by
  have hs := directFirst_contract spec true budget code hc
  change (budget < spec.decode code ↔ (spec.directStrict budget).1 ≤ code) at hs
  have hn : spec.decode code ≤ budget ↔ code < (spec.directStrict budget).1 := by
    rw [← not_lt, hs, not_le]
  rw [hn]
  unfold RankUniverse.directCap
  omega

theorem directCap_nonnegative (spec : RankUniverse) (budget : ℚ) (hb : 0 ≤ budget) : 0 ≤ spec.directCap budget := by
  exact (directCap_exact spec budget 0 (by omega)).mp (by simpa only [decode_zero] using hb)

theorem directWeak_eq (spec : RankUniverse) (threshold : ℚ) :
    (spec.directWeak threshold).1 = (spec.weak threshold).1 := by
  have hn := directFirst_bound spec false threshold
  have ho := MonotoneResourceCuts.weak_contract (rankCap spec.order) spec.decode (decode_mono spec) threshold
  change (spec.directWeak threshold).1 ≤ rankCap spec.order + 1 at hn
  have hOldBound : (spec.weak threshold).1 ≤ rankCap spec.order + 1 := ho.1
  apply le_antisymm
  · by_cases h : (spec.weak threshold).1 = rankCap spec.order + 1
    · rwa [h]
    · have hc : (spec.weak threshold).1 ≤ rankCap spec.order := by omega
      exact (directFirst_contract spec false threshold _ hc).mp ((ho.2 _ hc).mpr le_rfl)
  · by_cases h : (spec.directWeak threshold).1 = rankCap spec.order + 1
    · rw [h]
      exact ho.1
    · have hc : (spec.directWeak threshold).1 ≤ rankCap spec.order := by omega
      exact (ho.2 _ hc).mp ((directFirst_contract spec false threshold _ hc).mpr le_rfl)

theorem directStrict_eq (spec : RankUniverse) (threshold : ℚ) :
    (spec.directStrict threshold).1 = (spec.strict threshold).1 := by
  have hn := directFirst_bound spec true threshold
  have ho := MonotoneResourceCuts.strict_contract (rankCap spec.order) spec.decode (decode_mono spec) threshold
  change (spec.directStrict threshold).1 ≤ rankCap spec.order + 1 at hn
  have hOldBound : (spec.strict threshold).1 ≤ rankCap spec.order + 1 := ho.1
  apply le_antisymm
  · by_cases h : (spec.strict threshold).1 = rankCap spec.order + 1
    · rwa [h]
    · have hc : (spec.strict threshold).1 ≤ rankCap spec.order := by omega
      exact (directFirst_contract spec true threshold _ hc).mp ((ho.2 _ hc).mpr le_rfl)
  · by_cases h : (spec.directStrict threshold).1 = rankCap spec.order + 1
    · rw [h]
      exact ho.1
    · have hc : (spec.directStrict threshold).1 ≤ rankCap spec.order := by omega
      exact (ho.2 _ hc).mp ((directFirst_contract spec true threshold _ hc).mpr le_rfl)

theorem directCap_eq (spec : RankUniverse) (budget : ℚ) : spec.directCap budget = spec.cap budget := by
  unfold RankUniverse.directCap RankUniverse.cap MonotoneResourceCuts.cap
  rw [directStrict_eq]
  rfl

end Blotto.Farey
