import Blotto.FareyResponseSlack
import Blotto.Model
import Blotto.ProductFiniteTraining
import Mathlib.Data.Finset.Max

/-! Proof-only finite threshold selection for arbitrary real deviations.
The labels of candidate rows are retained, including duplicate anchors. -/

namespace Blotto.Farey

open scoped BigOperators

/-- Add a labelled zero to any finite anchor family. -/
def zeroExtendedAnchor {n : ℕ} (anchor : Fin n → Fraction) : Option (Fin n) → Fraction
  | none => zeroFraction
  | some i => anchor i

/-- A greatest affordable anchor, with zero included in its finite search.
This is a proof witness, not an algorithm on arbitrary exact real inputs. -/
structure RealAnchorPredecessor {n : ℕ} (D : ℕ) (anchor : Fin n → Fraction) (y : ℝ) where
  threshold : Fraction
  bounded : threshold.den ≤ D
  below : (threshold.value : ℝ) ≤ y
  greatest : ∀ i, ((anchor i).value : ℝ) ≤ y → (anchor i).value ≤ threshold.value
  selected : threshold = zeroFraction ∨ ∃ i, threshold = anchor i

theorem exists_realAnchorPredecessor (D n : ℕ) (hD : 0 < D)
    (anchor : Fin n → Fraction) (hDen : ∀ i, (anchor i).den ≤ D)
    (y : ℝ) (hy : 0 ≤ y) : Nonempty (RealAnchorPredecessor D anchor y) := by
  classical
  let eligible : Finset (Option (Fin n)) :=
    Finset.univ.filter (fun i => ((zeroExtendedAnchor anchor i).value : ℝ) ≤ y)
  have hZero : (none : Option (Fin n)) ∈ eligible := by
    simp [eligible, zeroExtendedAnchor, zeroFraction, Fraction.value, hy]
  obtain ⟨i, hi, hMax⟩ := Finset.exists_max_image eligible
    (fun k => ((zeroExtendedAnchor anchor k).value : ℝ)) ⟨none, hZero⟩
  refine ⟨⟨zeroExtendedAnchor anchor i, ?_, ?_, ?_, ?_⟩⟩
  · cases i
    · change 1 ≤ D
      omega
    · exact hDen _
  · exact (Finset.mem_filter.mp hi).2
  · intro k hk
    have hm := hMax (some k)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    exact_mod_cast hm
  · cases i
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩

noncomputable def realAnchorPredecessor (D n : ℕ) (hD : 0 < D)
    (anchor : Fin n → Fraction) (hDen : ∀ i, (anchor i).den ≤ D)
    (y : ℝ) (hy : 0 ≤ y) : RealAnchorPredecessor D anchor y :=
  Classical.choice (exists_realAnchorPredecessor D n hD anchor hDen y hy)

/-- Closed precisely at an exact anchor; otherwise the affordable predecessor
is an open threshold. -/
noncomputable def RealAnchorPredecessor.isOpen {D n : ℕ} {anchor : Fin n → Fraction} {y : ℝ}
    (p : RealAnchorPredecessor D anchor y) : Bool :=
  if (p.threshold.value : ℝ) = y then false else true

theorem RealAnchorPredecessor.open_iff {D n : ℕ} {anchor : Fin n → Fraction} {y : ℝ}
    (p : RealAnchorPredecessor D anchor y) :
    p.isOpen = true ↔ (p.threshold.value : ℝ) < y := by
  classical
  unfold RealAnchorPredecessor.isOpen
  split_ifs with he
  · simp [he]
  · exact ⟨fun _ => lt_of_le_of_ne p.below he, fun _ => rfl⟩

/-- The selected closed/open option preserves every candidate anchor's
canonical two-player share, including a zero half tie. -/
theorem RealAnchorPredecessor.share_exact {n : ℕ} (spec : RankUniverse)
    (anchor : Fin n → Fraction) (hDen : ∀ i, (anchor i).den ≤ spec.order)
    (y : ℝ) (p : RealAnchorPredecessor spec.order anchor y) (hShift : 0 < spec.shift) :
    ∀ i, share y ((anchor i).value : ℝ) =
      share (responseOptionBid spec p.threshold p.isOpen : ℝ) ((anchor i).value : ℝ) := by
  classical
  intro i
  by_cases he : (p.threshold.value : ℝ) = y
  · have hClosed : p.isOpen = false := by simp [RealAnchorPredecessor.isOpen, he]
    simp only [hClosed, responseOptionBid, Bool.false_eq_true, ite_false, add_zero]
    rw [he]
  · have hOpen : p.isOpen = true := by simp [RealAnchorPredecessor.isOpen, he]
    have hStrict : (p.threshold.value : ℝ) < y := p.open_iff.mp hOpen
    have hBid := response_open_comparisons spec p.threshold (anchor i) p.bounded (hDen i) hShift
    have hOriginal : ((anchor i).value : ℝ) < y ↔ (anchor i).value ≤ p.threshold.value := by
      constructor
      · intro hi
        exact p.greatest i hi.le
      · intro hi
        have hiReal : ((anchor i).value : ℝ) ≤ (p.threshold.value : ℝ) := by exact_mod_cast hi
        exact hiReal.trans_lt hStrict
    have hWin : ((anchor i).value : ℝ) < y ↔
        ((anchor i).value : ℝ) < (responseOptionBid spec p.threshold true : ℝ) := by
      rw [hOriginal]
      exact hBid.1.symm.trans (by norm_cast)
    have hOriginalNe : y ≠ ((anchor i).value : ℝ) := by
      intro hi
      have hBelow := p.greatest i (by rw [hi])
      have hBelowReal : ((anchor i).value : ℝ) ≤ (p.threshold.value : ℝ) := by exact_mod_cast hBelow
      linarith
    have hBidNe : (responseOptionBid spec p.threshold true : ℝ) ≠ ((anchor i).value : ℝ) := by
      exact_mod_cast hBid.2
    simp only [hOpen, share, hOriginalNe, hBidNe, ite_false]
    simp only [hWin]

/-- Lowering every real bid to its selected affordable threshold preserves the
budget inequality. If one bid is open, one coordinate is lowered strictly, so
the aggregate threshold budget has strictly positive slack. -/
theorem realAnchorPredecessor_tuple_feasible (D m n : ℕ) (B : ℚ)
    (anchor : Fin m → Fin n → Fraction) (y : Allocation m)
    (p : (j : Fin m) → RealAnchorPredecessor D (anchor j) (y j))
    (hBudget : (∑ j, y j) ≤ (B : ℝ)) :
    ResponseOptionFeasible B (fun j => (p j).threshold) (fun j => (p j).isOpen) := by
  have hSum : (∑ j, ((p j).threshold.value : ℝ)) ≤ (∑ j, y j) :=
    Finset.sum_le_sum (fun j _ => (p j).below)
  constructor
  · exact_mod_cast hSum.trans hBudget
  · rintro ⟨j, hj⟩
    have hStrict : (∑ k, ((p k).threshold.value : ℝ)) < (∑ k, y k) :=
      Finset.sum_lt_sum (fun k _ => (p k).below)
        ⟨j, Finset.mem_univ j, (p j).open_iff.mp hj⟩
    exact_mod_cast hStrict.trans_le hBudget

/-- Every nonnegative hard-budget real deviation has an actual feasible
source-universe code tuple with exactly the same shares against every row of
a finite bounded-Farey candidate family. No response-soundness premise is used. -/
theorem continuous_response_represented (D m n q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (hBunit : B ≤ 1)
    (anchor : Fin n → Fin m → Fraction) (hDen : ∀ i j, (anchor i j).den ≤ D)
    (y : Allocation m) (hy : Feasible (B : ℝ) y) :
    ∃ code : Fin m → ℕ,
      (∀ j, code j ≤ rankCap D) ∧
      Feasible (B : ℝ) (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) ∧
      (∀ i j, share (y j) ((anchor i j).value : ℝ) =
        share ((responseUniverse D m q hD hm hq).decode (code j) : ℝ) ((anchor i j).value : ℝ)) := by
  let p : (j : Fin m) → RealAnchorPredecessor D (fun i => anchor i j) (y j) :=
    fun j => realAnchorPredecessor D n hD (fun i => anchor i j) (fun i => hDen i j) (y j) (hy.1 j)
  let threshold : Fin m → Fraction := fun j => (p j).threshold
  let isOpen : Fin m → Bool := fun j => (p j).isOpen
  have hOptions : ResponseOptionFeasible B threshold isOpen :=
    realAnchorPredecessor_tuple_feasible D m n B (fun j i => anchor i j) y p hy.2
  have hRep := responseOptionTuple_represented D m q hD hm hq B hBden hBunit threshold
    (fun j => (p j).bounded) isOpen hOptions
  refine ⟨fun j => responseOptionCode D (threshold j) (isOpen j), hRep.1, ⟨?_, ?_⟩, ?_⟩
  · intro j
    change (0 : ℝ) ≤ ((responseUniverse D m q hD hm hq).decode
      (responseOptionCode D (threshold j) (isOpen j)) : ℝ)
    exact_mod_cast decode_nonnegative (responseUniverse D m q hD hm hq)
      (responseOptionCode D (threshold j) (isOpen j))
  · change (∑ j, ((responseUniverse D m q hD hm hq).decode
      (responseOptionCode D (threshold j) (isOpen j)) : ℝ)) ≤ (B : ℝ)
    exact_mod_cast hRep.2.2
  · intro i j
    rw [hRep.2.1 j]
    exact (p j).share_exact (responseUniverse D m q hD hm hq) (fun i => anchor i j)
      (fun i => hDen i j) (y j) (response_shift_positive D m q hD hm hq) i

/-- Rowwise payoff equality holds for arbitrary canonical positive common
values, not merely the field weights used during training. -/
theorem continuous_response_payoff_represented (D m n q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (hBunit : B ≤ 1)
    (anchor : Fin n → Fin m → Fraction) (hDen : ∀ i j, (anchor i j).den ≤ D)
    (v : Values m) (y : Allocation m) (hy : Feasible (B : ℝ) y) :
    ∃ code : Fin m → ℕ,
      (∀ j, code j ≤ rankCap D) ∧
      Feasible (B : ℝ) (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) ∧
      (∀ i, payoff v y (fun j => ((anchor i j).value : ℝ)) =
        payoff v (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ))
          (fun j => ((anchor i j).value : ℝ))) := by
  obtain ⟨code, hBound, hBudget, hShare⟩ :=
    continuous_response_represented D m n q hD hm hq B hBden hBunit anchor hDen y hy
  refine ⟨code, hBound, hBudget, ?_⟩
  intro i
  unfold payoff
  apply Finset.sum_congr rfl
  intro j _
  rw [hShare i j]

/-- The same single response preserves expected payoff for a complete finite
whole-row law; candidate probabilities and duplicate labels are unchanged. -/
theorem continuous_response_law_payoff_represented (D m n q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (hBunit : B ≤ 1)
    (anchor : Fin n → Fin m → Fraction) (hDen : ∀ i j, (anchor i j).den ≤ D)
    (law : RationalWholeRowLaw n m) (hRow : ∀ i j, law.row i j = (anchor i j).value)
    (v : Values m) (y : Allocation m) (hy : Feasible (B : ℝ) y) :
    ∃ code : Fin m → ℕ,
      (∀ j, code j ≤ rankCap D) ∧
      Feasible (B : ℝ) (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) ∧
      purePayoff v y law.law = purePayoff v
        (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) law.law := by
  obtain ⟨code, hBound, hBudget, hPayoff⟩ :=
    continuous_response_payoff_represented D m n q hD hm hq B hBden hBunit anchor hDen v y hy
  refine ⟨code, hBound, hBudget, ?_⟩
  rw [law.purePayoff_eq_sum, law.purePayoff_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hRealRow : law.realRow i = (fun j => ((anchor i j).value : ℝ)) := by
    funext j
    change (law.row i j : ℝ) = ((anchor i j).value : ℝ)
    rw [hRow i j]
  rw [hRealRow, hPayoff i]

/-- Every actual closed candidate-universe decoding is a bounded Farey
fraction. This derives the candidate membership required by the response
envelope, including its terminal one code. -/
theorem candidate_decode_fraction (D : ℕ) (hD : 0 < D) (code : ℕ) :
    ∃ fraction : Fraction, fraction.den ≤ D ∧
      fraction.value = (candidateUniverse D hD).decode code := by
  by_cases hCode : code < rankCap D
  · let spec := candidateUniverse D hD
    let base := spec.base code hCode
    refine ⟨base, (base_bounds spec code hCode).1, ?_⟩
    change base.value = (if hk : code < rankCap D then spec.bump code (spec.base code hk) else 1)
    simp only [hCode, dite_true]
    have hBounds := bump_bounds spec code base
    have hShift : spec.shift = 0 := rfl
    rw [hShift, add_zero] at hBounds
    exact le_antisymm hBounds.1 hBounds.2
  · refine ⟨oneFraction, ?_, ?_⟩
    · change 1 ≤ D
      omega
    · simp [RankUniverse.decode, candidateUniverse, hCode, oneFraction, Fraction.value]

/-- Concrete closed candidate codes need no supplied Farey-membership or
continuous-response soundness oracle. -/
theorem candidate_codes_continuous_response_represented (D m n q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (hBunit : B ≤ 1)
    (candidateCode : Fin n → Fin m → ℕ) (v : Values m)
    (y : Allocation m) (hy : Feasible (B : ℝ) y) :
    ∃ code : Fin m → ℕ,
      (∀ j, code j ≤ rankCap D) ∧
      Feasible (B : ℝ) (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) ∧
      (∀ i, payoff v y (fun j => ((candidateUniverse D hD).decode (candidateCode i j) : ℝ)) =
        payoff v (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ))
          (fun j => ((candidateUniverse D hD).decode (candidateCode i j) : ℝ))) := by
  classical
  let anchor : Fin n → Fin m → Fraction :=
    fun i j => Classical.choose (candidate_decode_fraction D hD (candidateCode i j))
  have hDen : ∀ i j, (anchor i j).den ≤ D :=
    fun i j => (Classical.choose_spec (candidate_decode_fraction D hD (candidateCode i j))).1
  have hValue : ∀ i j, (anchor i j).value = (candidateUniverse D hD).decode (candidateCode i j) :=
    fun i j => (Classical.choose_spec (candidate_decode_fraction D hD (candidateCode i j))).2
  obtain ⟨code, hBound, hBudget, hPayoff⟩ :=
    continuous_response_payoff_represented D m n q hD hm hq B hBden hBunit anchor hDen v y hy
  refine ⟨code, hBound, hBudget, ?_⟩
  intro i
  simpa only [hValue] using hPayoff i

/-- The concrete closed candidate decoder gives exact expected-payoff
representation against any supplied finite whole-row law using those labels. -/
theorem candidate_law_continuous_response_represented (D m n q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (hBunit : B ≤ 1)
    (candidateCode : Fin n → Fin m → ℕ) (law : RationalWholeRowLaw n m)
    (hRow : ∀ i j, law.row i j = (candidateUniverse D hD).decode (candidateCode i j))
    (v : Values m) (y : Allocation m) (hy : Feasible (B : ℝ) y) :
    ∃ code : Fin m → ℕ,
      (∀ j, code j ≤ rankCap D) ∧
      Feasible (B : ℝ) (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) ∧
      purePayoff v y law.law = purePayoff v
        (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) law.law := by
  obtain ⟨code, hBound, hBudget, hPayoff⟩ :=
    candidate_codes_continuous_response_represented D m n q hD hm hq B hBden hBunit candidateCode v y hy
  refine ⟨code, hBound, hBudget, ?_⟩
  rw [law.purePayoff_eq_sum, law.purePayoff_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hRealRow : law.realRow i = (fun j => ((candidateUniverse D hD).decode (candidateCode i j) : ℝ)) := by
    funext j
    change (law.row i j : ℝ) = _
    rw [hRow i j]
  rw [hRealRow, hPayoff i]

/-- A bound verified on the actual finite feasible response-code set controls
every canonical real hard-budget deviation. The response-envelope implication
is proved here, rather than supplied as a soundness certificate. -/
theorem candidate_law_continuous_bound (D m n q : ℕ)
    (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (B : ℚ) (hBden : B.den ∣ q) (hBunit : B ≤ 1)
    (candidateCode : Fin n → Fin m → ℕ) (law : RationalWholeRowLaw n m)
    (hRow : ∀ i j, law.row i j = (candidateUniverse D hD).decode (candidateCode i j))
    (v : Values m) (bound : ℝ)
    (hFinite : ∀ code : Fin m → ℕ, (∀ j, code j ≤ rankCap D) →
      Feasible (B : ℝ) (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) →
      purePayoff v (fun j => ((responseUniverse D m q hD hm hq).decode (code j) : ℝ)) law.law ≤ bound) :
    ∀ y : Allocation m, Feasible (B : ℝ) y → purePayoff v y law.law ≤ bound := by
  intro y hy
  obtain ⟨code, hCode, hBudget, hPayoff⟩ :=
    candidate_law_continuous_response_represented D m n q hD hm hq B hBden hBunit candidateCode law hRow v y hy
  rw [hPayoff]
  exact hFinite code hCode hBudget

end Blotto.Farey
