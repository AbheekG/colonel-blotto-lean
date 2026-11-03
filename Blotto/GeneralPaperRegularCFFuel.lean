import Blotto.GeneralPaperRegularCFLoop

/-! Constructed global fuel is sufficient for the actual arithmetic CF loop.
Every continuing Euclidean step uses the proved arithmetic quotient/remainder;
two continuing steps halve the denominator. No input encoding-length query
or supplied termination/call-count oracle is used.
-/
namespace Blotto.GeneralPaperRegularCFFuel
open GeneralPaperRegularCFLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

def PairBound (width : ℕ) (state : State) : Prop :=
  state.numerator<2^width ∧ state.denominator<2^width

def Stops (D divisionFuel : ℕ) : ℕ → State → Prop
  | 0,_ => False
  | fuel+1,state => (advance D divisionFuel state).2=false ∨ Stops D divisionFuel fuel (advance D divisionFuel state).1

theorem quotient_cap (width n d : ℕ) (hn : n<2^width) (hd : 0<d) : n<d*2^(width+2) := by
  have hp : 2^width≤2^(width+2) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  have hm : 2^(width+2)≤d*2^(width+2) := by
    have he := Nat.mul_le_mul_right (2^(width+2)) hd
    simpa only [Nat.one_mul] using he
  exact hn.trans_le (hp.trans hm)

theorem continuing_positive (D divisionFuel : ℕ) (state : State) (hMore : (advance D divisionFuel state).2=true) :
    0<state.denominator := by
  by_contra h
  have hz : state.denominator=0 := by omega
  simp only [advance,ite_eq_left hz,Bool.false_eq_true] at hMore

theorem advance_pair_bound (D width : ℕ) (state : State) (hBound : PairBound width state) :
    PairBound width (advance D (width+2) state).1 := by
  by_cases hz : state.denominator=0
  · simpa only [advance,ite_eq_left hz,PairBound] using hBound
  · have hp : 0<state.denominator := by omega
    have he := advance_euclidean D (width+2) state hp (quotient_cap width _ _ hBound.1 hp)
    exact ⟨he.1 ▸ hBound.2,he.2 ▸ (Nat.mod_lt state.numerator hp).trans hBound.2⟩

theorem two_remainders_half (d r : ℕ) (hr : 0<r) (hSmall : r<d) : 2*(d%r)<d := by
  by_cases hh : 2*r≤d
  · have he := Nat.mod_lt d hr
    omega
  · have he : d-r<r := by omega
    rw [Nat.mod_eq_sub_mod hSmall.le,Nat.mod_eq_of_lt he]
    omega

theorem continuing_two_halves (D width : ℕ) (state : State) (hBound : PairBound width state)
    (hFirst : (advance D (width+2) state).2=true)
    (hSecond : (advance D (width+2) (advance D (width+2) state).1).2=true) :
    2*(advance D (width+2) (advance D (width+2) state).1).1.denominator<state.denominator := by
  have hp := continuing_positive D (width+2) state hFirst
  have hNext := advance_pair_bound D width state hBound
  have hq := continuing_positive D (width+2) (advance D (width+2) state).1 hSecond
  have he := advance_euclidean D (width+2) state hp (quotient_cap width _ _ hBound.1 hp)
  have hf := advance_euclidean D (width+2) (advance D (width+2) state).1 hq (quotient_cap width _ _ hNext.1 hq)
  rw [hf.2,he.1]
  exact two_remainders_half _ _ hq (he.2 ▸ Nat.mod_lt state.numerator hp)

theorem stops_mono (D divisionFuel fuel extra : ℕ) (state : State) (hFuel : fuel≤extra) (hStops : Stops D divisionFuel fuel state) :
    Stops D divisionFuel extra state := by
  induction fuel generalizing state extra with
  | zero => exact hStops.elim
  | succ fuel ih =>
    cases extra with
    | zero => omega
    | succ extra =>
      exact hStops.elim Or.inl (fun h => Or.inr (ih extra _ (by omega) h))

theorem stops_by_denominator (D width k : ℕ) (state : State) (hBound : PairBound width state) (hDen : state.denominator<2^k) :
    Stops D (width+2) (2*k+1) state := by
  induction k generalizing state with
  | zero =>
    have hz : state.denominator=0 := by simpa only [pow_zero] using Nat.eq_zero_of_le_zero (by omega : state.denominator≤0)
    exact Or.inl (advance_zero_stop D (width+2) state hz).1
  | succ k ih =>
    have hFuel : 2*(k+1)+1=(2*k+1)+2 := by omega
    rw [hFuel]
    change (advance D (width+2) state).2=false ∨
      (advance D (width+2) (advance D (width+2) state).1).2=false ∨
        Stops D (width+2) (2*k+1) (advance D (width+2) (advance D (width+2) state).1).1
    by_cases hFirst : (advance D (width+2) state).2=false
    · exact Or.inl hFirst
    · by_cases hSecond : (advance D (width+2) (advance D (width+2) state).1).2=false
      · exact Or.inr (Or.inl hSecond)
      · have hf : (advance D (width+2) state).2=true := by cases h : (advance D (width+2) state).2 <;> simp_all
        have hs : (advance D (width+2) (advance D (width+2) state).1).2=true := by
          cases h : (advance D (width+2) (advance D (width+2) state).1).2 <;> simp_all
        have hHalf := continuing_two_halves D width state hBound hf hs
        have hNext := advance_pair_bound D width _ (advance_pair_bound D width state hBound)
        have hSmall : (advance D (width+2) (advance D (width+2) state).1).1.denominator<2^k := by
          rw [pow_succ] at hDen
          omega
        exact Or.inr (Or.inr (ih _ hNext hSmall))

theorem midpoint_pair_bound (C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) : PairBound lambda (initial C t) := by
  simp only [PairBound,initial]
  rw [←hPower]
  omega

theorem midpoint_stops (D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    Stops D (lambda+2) (2*lambda+4) (initial C t) := by
  have hp := midpoint_pair_bound C t lambda hC ht hPower
  exact stops_mono D (lambda+2) (2*lambda+1) (2*lambda+4) (initial C t) (by omega)
    (stops_by_denominator D lambda lambda (initial C t) hp hp.2)

theorem stopped_result (D divisionFuel fuel : ℕ) (state : State) (hStops : Stops D divisionFuel fuel state) :
    ∃ last, (advance D divisionFuel last).2=false ∧ run D divisionFuel fuel state=(advance D divisionFuel last).1 := by
  induction fuel generalizing state with
  | zero => exact hStops.elim
  | succ fuel ih =>
    cases hb : (advance D divisionFuel state).2 with
    | false => exact ⟨state,hb,by simp only [run,hb,Bool.false_eq_true,ite_false]⟩
    | true =>
      have hh : Stops D divisionFuel fuel (advance D divisionFuel state).1 := by
        exact hStops.elim (fun h => by simp only [hb,Bool.true_eq_false] at h) id
      obtain ⟨last,hLast,hRun⟩ := ih _ hh
      exact ⟨last,hLast,by simpa only [run,hb,ite_true] using hRun⟩

end Blotto.GeneralPaperRegularCFFuel
