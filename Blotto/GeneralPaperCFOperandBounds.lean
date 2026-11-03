import Blotto.GeneralPaperConstructedNatDivisionBits

/-! Original-pair bounds for all reached midpoint-CF operands. Conserved
linear identities bound both continuants and each raw product before its
addition, including the last rejected convergent. No growth-by-history
recurrence or assumed bounded-continuant certificate is used.
-/
namespace Blotto.GeneralPaperCFOperandBounds
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFLinearInvariant
set_option autoImplicit false
set_option maxHeartbeats 6000000

structure Valid (width N M : ℕ) (s : State) : Prop where
  pair : PairBound width s
  linear : Linear N M s
  positive : 0<s.numerator
  olderNum : s.olderNum≤N
  olderDen : s.olderDen≤M
  selected : ∀ f, s.selected=some f → f.num≤N ∧ f.den≤M

theorem previous (width N M : ℕ) (s : State) (h : Valid width N M s) :
    s.previousNum≤N ∧ s.previousDen≤M := previous_bounds N M s h.linear h.positive

theorem advance_valid (D width N M : ℕ) (s : State) (h : Valid width N M s) :
    Valid width N M (advance D (width+2) s).1 := by
  have hPair := advance_pair_bound D width s h.pair
  have hLinear := advance_linear D width N M s h.pair h.linear
  have hPos := advance_numerator_positive D (width+2) s h.positive
  have hPrev := previous width N M s h
  have hNext := previous_bounds N M (advance D (width+2) s).1 hLinear hPos
  have hOlder : (advance D (width+2) s).1.olderNum≤N ∧ (advance D (width+2) s).1.olderDen≤M := by
    by_cases hz : s.denominator=0
    · simpa only [advance,ite_eq_left hz] using And.intro h.olderNum h.olderDen
    · have hc := GeneralPaperCFAdvanceData.continuants D (width+2) s (by omega)
      rw [hc.1,hc.2.1]
      exact hPrev
  refine ⟨hPair,hLinear,hPos,hOlder.1,hOlder.2,?_⟩
  cases hs : (advance D (width+2) s).2 with
  | false =>
    rw [GeneralPaperCFAdvanceData.stopped_selection D (width+2) s hs]
    exact h.selected
  | true =>
    obtain ⟨g,hg,hn,hd⟩ := GeneralPaperCFAdvanceData.continuing_selection D (width+2) s hs
    intro f hf
    have he : g=f := Option.some.inj (hg.symm.trans hf)
    subst f
    rw [hn,hd]
    exact hNext

theorem run_valid (D width fuel N M : ℕ) (s : State) (h : Valid width N M s) :
    Valid width N M (run D (width+2) fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    rw [run]
    split
    · exact ih _ (advance_valid D width N M s h)
    · exact advance_valid D width N M s h

theorem initial_valid (C t width : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^width) :
    Valid width (2*t+1) (2*C) (initial C t) := by
  refine ⟨midpoint_pair_bound C t width hC ht hPower,initial_linear C t,?_,?_,?_,?_⟩
  · dsimp only [initial]; omega
  · exact Nat.zero_le _
  · change 1≤2*C; omega
  · intro f hf; cases hf

theorem raw_products (D width N M : ℕ) (s : State) (h : Valid width N M s) (hd : 0<s.denominator) :
    let q := (GeneralPaperConstructedNatDivision.run s.numerator s.denominator (width+2)).quotient
    q≤s.numerator ∧ q*s.previousNum≤N ∧ q*s.previousDen≤M ∧
      q*s.previousNum+s.olderNum≤N ∧ q*s.previousDen+s.olderDen≤M := by
  let q := (GeneralPaperConstructedNatDivision.run s.numerator s.denominator (width+2)).quotient
  have hSpec := GeneralPaperConstructedNatDivision.run_spec s.numerator s.denominator (width+2) hd
    (quotient_cap width _ _ h.pair.1 hd)
  have hProduct : s.denominator*q≤s.numerator := by dsimp only [q]; omega
  have hQ : q≤s.numerator := by
    have hh : q≤s.denominator*q := by
      simpa only [one_mul] using Nat.mul_le_mul_right q (show 1≤s.denominator by omega)
    exact hh.trans hProduct
  have hNext := previous width N M _ (advance_valid D width N M s h)
  have hc := GeneralPaperCFAdvanceData.continuants D (width+2) s hd
  rw [hc.2.2.1,hc.2.2.2] at hNext
  dsimp only
  exact ⟨hQ,by omega,by omega,hNext.1,hNext.2⟩

theorem midpoint_all_prefixes (D C t width fuel : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^width) :
    Valid width (2*t+1) (2*C) (run D (width+2) fuel (initial C t)) :=
  run_valid D width fuel (2*t+1) (2*C) (initial C t) (initial_valid C t width hC ht hPower)

end Blotto.GeneralPaperCFOperandBounds
