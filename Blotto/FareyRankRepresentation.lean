import Blotto.FareyRankUniverse

/-! Every bounded-denominator closed bid and every allowed shifted bid has
its actual R127 distinguished-code preimage. The decoder's many-to-one labels
are retained. This is the exact Farey representation, not a surrogate grid. -/

namespace Blotto.Farey

theorem closedCode_cutoff (D : ℕ) (hD : 0 < D) (bid : Fraction) (code : ℕ) :
    closedCode D bid ≤ code ↔ bid.value < rankCutoff D code := by
  have hH : (0 : ℚ) < rankScale D := by unfold rankScale; positivity
  have hn : (0 : ℚ) ≤ (rankScale D : ℚ) * bid.value := mul_nonneg hH.le (value_nonnegative bid)
  have hNat : 2 * Nat.floor ((rankScale D : ℚ) * bid.value) ≤ code ↔
      Nat.floor ((rankScale D : ℚ) * bid.value) < code / 2 + 1 := by omega
  unfold closedCode rankCutoff
  rw [hNat, Nat.floor_lt hn, lt_div_iff₀ hH, mul_comm bid.value]

theorem closedCode_le_rankCap (D : ℕ) (_hD : 0 < D) (bid : Fraction) (hBid : bid.value ≤ 1) :
    closedCode D bid ≤ rankCap D := by
  have hH : (0 : ℚ) ≤ rankScale D := by positivity
  have hs : (rankScale D : ℚ) * bid.value ≤ (rankScale D : ℚ) := by nlinarith
  have hf := Nat.floor_mono hs
  rw [Nat.floor_natCast] at hf
  unfold closedCode rankCap
  omega

theorem closedCode_lt_rankCap (D : ℕ) (hD : 0 < D) (bid : Fraction) (hBid : bid.value < 1) :
    closedCode D bid < rankCap D := by
  have hH : (0 : ℚ) < rankScale D := by unfold rankScale; positivity
  have hn : (0 : ℚ) ≤ (rankScale D : ℚ) * bid.value := mul_nonneg hH.le (value_nonnegative bid)
  have hs : (rankScale D : ℚ) * bid.value < (rankScale D : ℚ) := by nlinarith
  have hf := (Nat.floor_lt hn).mpr hs
  unfold closedCode rankCap
  omega

theorem base_value_at_rank (spec : RankUniverse) (bid : Fraction) (hBid : bid.den ≤ spec.order)
    (code : ℕ) (hCode : code < rankCap spec.order)
    (hLower : closedCode spec.order bid ≤ code) (hUpper : code < closedCode spec.order bid + 8) :
    (spec.base code hCode).value = bid.value := by
  have hBidBelow := (closedCode_cutoff spec.order spec.order_positive bid code).mp hLower
  have hBaseBelow := (base_bounds spec code hCode).2
  have hBaseDen := (base_bounds spec code hCode).1
  have hBaseCode := (closedCode_cutoff spec.order spec.order_positive (spec.base code hCode) code).mpr hBaseBelow
  have hAtLeast : bid.value ≤ (spec.base code hCode).value :=
    (predecessor spec.order spec.order_positive (rankCutoff spec.order code)
      (rankCutoff_valid spec.order spec.order_positive code hCode)).greatest bid hBid hBidBelow
  apply le_antisymm _ hAtLeast
  by_contra hg
  have hGreater : bid.value < (spec.base code hCode).value := lt_of_not_ge hg
  have hGap := closedCode_separation spec.order hBid hBaseDen hGreater
  omega

theorem decode_closed_bid (spec : RankUniverse) (bid : Fraction) (hBid : bid.den ≤ spec.order)
    (hUnit : bid.value ≤ 1) : spec.decode (closedCode spec.order bid) = bid.value := by
  by_cases hOne : bid.value = 1
  · have hCode : closedCode spec.order bid = rankCap spec.order := by
      simp only [closedCode, hOne, mul_one, Nat.floor_natCast, rankCap]
    rw [hCode, decode_terminal, hOne]
  · have hLt : bid.value < 1 := lt_of_le_of_ne hUnit hOne
    have hc := closedCode_lt_rankCap spec.order spec.order_positive bid hLt
    have hBase := base_value_at_rank spec bid hBid _ hc le_rfl (by omega)
    have hBaseCode : closedCode spec.order (spec.base (closedCode spec.order bid) hc) = closedCode spec.order bid := by
      exact congrArg (fun value : ℚ => 2 * Nat.floor ((rankScale spec.order : ℚ) * value)) hBase
    unfold RankUniverse.decode
    simp only [hc, dite_true]
    unfold RankUniverse.bump
    have hImpossible : ¬ (0 < spec.shift ∧ closedCode spec.order (spec.base (closedCode spec.order bid) hc) + 1 ≤
      closedCode spec.order bid ∧ (spec.base (closedCode spec.order bid) hc).value + spec.shift ≤ 1) := by
      rw [hBaseCode]
      omega
    simp only [hImpossible, ite_false]
    exact hBase

theorem shiftedCode_valid (spec : RankUniverse) (bid : Fraction) (hShift : 0 < spec.shift)
    (hUnit : bid.value + spec.shift ≤ 1) : closedCode spec.order bid + 1 < rankCap spec.order := by
  have hLt : bid.value < 1 := by linarith
  have hCode := closedCode_lt_rankCap spec.order spec.order_positive bid hLt
  unfold closedCode rankCap at *
  omega

theorem decode_shifted_bid (spec : RankUniverse) (bid : Fraction) (hBid : bid.den ≤ spec.order)
    (hShift : 0 < spec.shift) (hUnit : bid.value + spec.shift ≤ 1) :
    spec.decode (closedCode spec.order bid + 1) = bid.value + spec.shift := by
  have hc := shiftedCode_valid spec bid hShift hUnit
  have hBase := base_value_at_rank spec bid hBid _ hc (by omega) (by omega)
  have hBaseCode : closedCode spec.order (spec.base (closedCode spec.order bid + 1) hc) = closedCode spec.order bid := by
    exact congrArg (fun value : ℚ => 2 * Nat.floor ((rankScale spec.order : ℚ) * value)) hBase
  unfold RankUniverse.decode
  simp only [hc, dite_true]
  unfold RankUniverse.bump
  have hBump : 0 < spec.shift ∧ closedCode spec.order (spec.base (closedCode spec.order bid + 1) hc) + 1 ≤
      closedCode spec.order bid + 1 ∧ (spec.base (closedCode spec.order bid + 1) hc).value + spec.shift ≤ 1 := by
    rw [hBaseCode, hBase]
    exact ⟨hShift, le_rfl, hUnit⟩
  rw [ite_eq_left hBump]
  exact congrArg (fun value : ℚ => value + spec.shift) hBase

theorem closed_bid_represented (spec : RankUniverse) (bid : Fraction) (hBid : bid.den ≤ spec.order)
    (hUnit : bid.value ≤ 1) : ∃ code ≤ rankCap spec.order, spec.decode code = bid.value :=
  ⟨closedCode spec.order bid, closedCode_le_rankCap spec.order spec.order_positive bid hUnit,
    decode_closed_bid spec bid hBid hUnit⟩

theorem shifted_bid_represented (spec : RankUniverse) (bid : Fraction) (hBid : bid.den ≤ spec.order)
    (hShift : 0 < spec.shift) (hUnit : bid.value + spec.shift ≤ 1) :
    ∃ code ≤ rankCap spec.order, spec.decode code = bid.value + spec.shift :=
  ⟨closedCode spec.order bid + 1, (shiftedCode_valid spec bid hShift hUnit).le,
    decode_shifted_bid spec bid hBid hShift hUnit⟩

end Blotto.Farey
