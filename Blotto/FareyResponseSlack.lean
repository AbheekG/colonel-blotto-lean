import Blotto.FareySourceUniverses
import Blotto.FareyRationalMembership

/-! The explicit denominator gap behind the R155 open-option response
semantics. The shift is the actual source response-universe shift; no response
soundness or gap oracle is supplied. -/

namespace Blotto.Farey

open scoped BigOperators

/-- The stored labelled denominators provide a common denominator for a sum. -/
theorem threshold_sum_den_dvd {ι : Type*} [DecidableEq ι]
    (fields : Finset ι) (threshold : ι → Fraction) :
    (∑ j ∈ fields, (threshold j).value).den ∣ ∏ j ∈ fields, (threshold j).den := by
  induction fields using Finset.induction_on with
  | empty => simp
  | @insert j fields hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul (value_den_dvd _) ih)

/-- A positive rational has an integer numerator of at least one. -/
theorem positive_rational_den_gap (x : ℚ) (hx : 0 < x) :
    1 / (x.den : ℚ) ≤ x := by
  have hn : (1 : ℤ) ≤ x.num := by have hp := Rat.num_pos.mpr hx; omega
  have hnq : (1 : ℚ) ≤ (x.num : ℚ) := by exact_mod_cast hn
  calc
    1 / (x.den : ℚ) ≤ (x.num : ℚ) / x.den :=
      div_le_div_of_nonneg_right hnq (by positivity)
    _ = x := x.num_div_den

/-- A strict threshold-budget gap is at least the reciprocal common denominator. -/
theorem threshold_gap_common_denominator (m q : ℕ) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (threshold : Fin m → Fraction)
    (hGap : (∑ j, (threshold j).value) < B) :
    1 / ((q : ℚ) * ∏ j, ((threshold j).den : ℚ)) ≤
      B - ∑ j, (threshold j).value := by
  have hp : 0 < ∏ j, (threshold j).den :=
    Finset.prod_pos (fun j _ => (threshold j).den_pos)
  have hd : (B - ∑ j, (threshold j).value).den ∣ q * ∏ j, (threshold j).den :=
    (Rat.sub_den_dvd _ _).trans
      (Nat.mul_dvd_mul hBden (threshold_sum_den_dvd Finset.univ threshold))
  have hle : (B - ∑ j, (threshold j).value).den ≤ q * ∏ j, (threshold j).den :=
    Nat.le_of_dvd (Nat.mul_pos hq hp) hd
  have hleq : ((B - ∑ j, (threshold j).value).den : ℚ) ≤
      (q : ℚ) * ∏ j, ((threshold j).den : ℚ) := by
    exact_mod_cast hle
  exact (one_div_le_one_div_of_le (by positivity) hleq).trans
    (positive_rational_den_gap _ (sub_pos.mpr hGap))

/-- Bounded threshold denominators turn the common-denominator gap into a
uniform gap depending only on the number of fields and the Farey order. -/
theorem threshold_gap_lower_bound (m q D : ℕ) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (threshold : Fin m → Fraction)
    (hDen : ∀ j, (threshold j).den ≤ D)
    (hGap : (∑ j, (threshold j).value) < B) :
    1 / ((q : ℚ) * (D : ℚ) ^ m) ≤ B - ∑ j, (threshold j).value := by
  have hp : (0 : ℚ) < (q : ℚ) * ∏ j, ((threshold j).den : ℚ) := by
    have hqp : (0 : ℚ) < q := by exact_mod_cast hq
    exact mul_pos hqp (Finset.prod_pos (fun j _ => by exact_mod_cast (threshold j).den_pos))
  have hProduct : (∏ j, (threshold j).den) ≤ D ^ m := by
    calc
      (∏ j, (threshold j).den) ≤ ∏ _j : Fin m, D := Finset.prod_le_prod (fun j _ => hDen j)
      _ = D ^ m := by simp
  have hProductQ : (q : ℚ) * ∏ j, ((threshold j).den : ℚ) ≤ (q : ℚ) * (D : ℚ) ^ m := by
    exact_mod_cast Nat.mul_le_mul_left q hProduct
  exact (one_div_le_one_div_of_le hp hProductQ).trans
    (threshold_gap_common_denominator m q hq B hBden threshold hGap)

/-- The actual shift denominator exceeds the amount needed for all m bumps. -/
theorem sourceShiftDenominator_gt_gap_scale (D m q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q) :
    m * q * D ^ m < sourceShiftDenominator D m q := by
  have hp : D ^ m ≤ D ^ (m + 2) :=
    pow_le_pow_right₀ (by omega : 1 ≤ D) (by omega)
  have hMul := Nat.mul_le_mul_left (2 * m * q) hp
  have hPos : 0 < m * q * D ^ m := by positivity
  unfold sourceShiftDenominator
  nlinarith

/-- Aggregate increments are strictly smaller than every legal threshold slack. -/
theorem response_shift_aggregate_lt_gap (D m q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (threshold : Fin m → Fraction)
    (hDen : ∀ j, (threshold j).den ≤ D)
    (hGap : (∑ j, (threshold j).value) < B) :
    (m : ℚ) * (responseUniverse D m q hD hm hq).shift <
      B - ∑ j, (threshold j).value := by
  have hQ : (0 : ℚ) < sourceShiftDenominator D m q := by
    unfold sourceShiftDenominator
    positivity
  have hScale : (0 : ℚ) < (q : ℚ) * (D : ℚ) ^ m := by positivity
  have hStrict : (m : ℚ) * ((q : ℚ) * (D : ℚ) ^ m) <
      (sourceShiftDenominator D m q : ℚ) := by
    have hNat := sourceShiftDenominator_gt_gap_scale D m q hD hm hq
    have hCast : (m : ℚ) * q * (D : ℚ) ^ m < (sourceShiftDenominator D m q : ℚ) := by
      exact_mod_cast hNat
    simpa only [mul_assoc] using hCast
  have hSmall : (m : ℚ) / sourceShiftDenominator D m q <
      1 / ((q : ℚ) * (D : ℚ) ^ m) := by
    apply (div_lt_div_iff₀ hQ hScale).mpr
    simpa only [one_mul] using hStrict
  change (m : ℚ) * (1 / (sourceShiftDenominator D m q : ℚ)) < _
  rw [mul_one_div]
  exact hSmall.trans_le (threshold_gap_lower_bound m q D hq B hBden threshold hDen hGap)

/-- A closed option uses its exact threshold; an open option uses the actual
source shift. In particular, a closed zero remains zero. -/
def responseOptionBid (spec : RankUniverse) (threshold : Fraction) (isOpen : Bool) : ℚ :=
  threshold.value + if isOpen then spec.shift else 0

/-- Distinguished labels for the closed and open threshold options. -/
def responseOptionCode (D : ℕ) (threshold : Fraction) (isOpen : Bool) : ℕ :=
  closedCode D threshold + if isOpen then 1 else 0

/-- Exact threshold feasibility: equality is permitted only for an all-closed
tuple. The resource here is the original threshold, before any positive bump. -/
def ResponseOptionFeasible {m : ℕ} (B : ℚ) (threshold : Fin m → Fraction)
    (isOpen : Fin m → Bool) : Prop :=
  (∑ j, (threshold j).value) ≤ B ∧
    ((∃ j, isOpen j = true) → (∑ j, (threshold j).value) < B)

theorem responseOptionBid_nonnegative (spec : RankUniverse) (threshold : Fraction) (isOpen : Bool) :
    0 ≤ responseOptionBid spec threshold isOpen := by
  unfold responseOptionBid
  cases isOpen <;> simp only [Bool.false_eq_true, ite_false, ite_true, add_zero]
  · exact value_nonnegative threshold
  · exact add_nonneg (value_nonnegative threshold) spec.shift_nonnegative

theorem responseOptionBid_closed_zero (spec : RankUniverse) :
    responseOptionBid spec zeroFraction false = 0 := by
  simp [responseOptionBid, zeroFraction, Fraction.value]

theorem responseOptionBid_open_zero (spec : RankUniverse) :
    responseOptionBid spec zeroFraction true = spec.shift := by
  simp [responseOptionBid, zeroFraction, Fraction.value]

/-- Any selection of open bumps costs at most the aggregate m-shift amount. -/
theorem responseOptionBid_sum_le (spec : RankUniverse) (m : ℕ)
    (threshold : Fin m → Fraction) (isOpen : Fin m → Bool) :
    (∑ j, responseOptionBid spec (threshold j) (isOpen j)) ≤
      (∑ j, (threshold j).value) + (m : ℚ) * spec.shift := by
  have hBump : (∑ j : Fin m, if isOpen j then spec.shift else 0) ≤ (m : ℚ) * spec.shift := by
    calc
      (∑ j : Fin m, if isOpen j then spec.shift else 0) ≤ ∑ _j : Fin m, spec.shift := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> linarith [spec.shift_nonnegative]
      _ = (m : ℚ) * spec.shift := by simp
  unfold responseOptionBid
  rw [Finset.sum_add_distrib]
  exact add_le_add le_rfl hBump

/-- The derived source shift realizes every feasible open/closed tuple within
the original at-most budget. -/
theorem responseOptionBid_source_feasible (D m q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (threshold : Fin m → Fraction)
    (hDen : ∀ j, (threshold j).den ≤ D) (isOpen : Fin m → Bool)
    (hFeasible : ResponseOptionFeasible B threshold isOpen) :
    (∑ j, responseOptionBid (responseUniverse D m q hD hm hq) (threshold j) (isOpen j)) ≤ B := by
  by_cases hAny : ∃ j, isOpen j = true
  · have hGap := response_shift_aggregate_lt_gap D m q hD hm hq B hBden threshold hDen (hFeasible.2 hAny)
    have hSum := responseOptionBid_sum_le (responseUniverse D m q hD hm hq) m threshold isOpen
    linarith
  · have hClosed : ∀ j, isOpen j = false := by
      intro j
      cases hj : isOpen j
      · rfl
      · exact False.elim (hAny ⟨j, hj⟩)
    simpa only [responseOptionBid, hClosed, Bool.false_eq_true, ite_false, add_zero] using hFeasible.1

/-- Each distinguished option label decodes exactly, including its tie-preserving
closed threshold and its strictly larger open threshold. -/
theorem responseOptionCode_exact (spec : RankUniverse) (threshold : Fraction)
    (hDen : threshold.den ≤ spec.order) (isOpen : Bool)
    (hShift : 0 < spec.shift) (hUnit : responseOptionBid spec threshold isOpen ≤ 1) :
    responseOptionCode spec.order threshold isOpen ≤ rankCap spec.order ∧
      spec.decode (responseOptionCode spec.order threshold isOpen) =
        responseOptionBid spec threshold isOpen := by
  cases isOpen
  · simp only [responseOptionBid, responseOptionCode, Bool.false_eq_true, ite_false, add_zero] at hUnit ⊢
    exact ⟨closedCode_le_rankCap spec.order spec.order_positive threshold hUnit,
      decode_closed_bid spec threshold hDen hUnit⟩
  · simp only [responseOptionBid, responseOptionCode, ite_true] at hUnit ⊢
    exact ⟨(shiftedCode_valid spec threshold hShift hUnit).le,
      decode_shifted_bid spec threshold hDen hShift hUnit⟩

/-- Actual response-universe codes realize the exact feasible threshold tuple.
No continuous-response soundness premise is part of this construction. -/
theorem responseOptionTuple_represented (D m q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (hBunit : B ≤ 1)
    (threshold : Fin m → Fraction) (hDen : ∀ j, (threshold j).den ≤ D)
    (isOpen : Fin m → Bool) (hFeasible : ResponseOptionFeasible B threshold isOpen) :
    (∀ j, responseOptionCode D (threshold j) (isOpen j) ≤ rankCap D) ∧
    (∀ j, (responseUniverse D m q hD hm hq).decode
      (responseOptionCode D (threshold j) (isOpen j)) =
        responseOptionBid (responseUniverse D m q hD hm hq) (threshold j) (isOpen j)) ∧
    (∑ j, (responseUniverse D m q hD hm hq).decode
      (responseOptionCode D (threshold j) (isOpen j))) ≤ B := by
  have hBudget := responseOptionBid_source_feasible D m q hD hm hq B hBden threshold hDen isOpen hFeasible
  have hExact : ∀ j, responseOptionCode D (threshold j) (isOpen j) ≤ rankCap D ∧
      (responseUniverse D m q hD hm hq).decode (responseOptionCode D (threshold j) (isOpen j)) =
        responseOptionBid (responseUniverse D m q hD hm hq) (threshold j) (isOpen j) := by
    intro j
    have hCoordinate := Finset.single_le_sum
      (fun k _ => responseOptionBid_nonnegative (responseUniverse D m q hD hm hq) (threshold k) (isOpen k))
      (Finset.mem_univ j)
    exact responseOptionCode_exact (responseUniverse D m q hD hm hq) (threshold j) (hDen j)
      (isOpen j) (response_shift_positive D m q hD hm hq) ((hCoordinate.trans hBudget).trans hBunit)
  refine ⟨fun j => (hExact j).1, fun j => (hExact j).2, ?_⟩
  simpa only [(hExact _).2] using hBudget

/-- A positive bump smaller than the Farey gap stays below every larger
bounded-denominator anchor. -/
theorem response_shift_before_next (spec : RankUniverse) (threshold other : Fraction)
    (hThreshold : threshold.den ≤ spec.order) (hOther : other.den ≤ spec.order)
    (hOrder : threshold.value < other.value) :
    threshold.value + spec.shift < other.value := by
  have hGap := bounded_separation spec.order hThreshold hOther hOrder
  linarith [spec.shift_small]

/-- An open option beats exactly the anchors weakly below its original
threshold, and it never creates a tie with any bounded-denominator anchor. -/
theorem response_open_comparisons (spec : RankUniverse) (threshold other : Fraction)
    (hThreshold : threshold.den ≤ spec.order) (hOther : other.den ≤ spec.order)
    (hShift : 0 < spec.shift) :
    (other.value < responseOptionBid spec threshold true ↔ other.value ≤ threshold.value) ∧
      responseOptionBid spec threshold true ≠ other.value := by
  simp only [responseOptionBid, ite_true]
  constructor
  · constructor
    · intro hBelow
      by_contra hNot
      have hNext := response_shift_before_next spec threshold other hThreshold hOther (lt_of_not_ge hNot)
      linarith
    · intro hBelow
      linarith
  · intro hEq
    rcases le_or_gt other.value threshold.value with hBelow | hAbove
    · linarith
    · have hNext := response_shift_before_next spec threshold other hThreshold hOther hAbove
      linarith

end Blotto.Farey
