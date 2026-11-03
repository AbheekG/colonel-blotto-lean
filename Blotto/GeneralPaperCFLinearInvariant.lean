import Blotto.GeneralPaperMidpointQuery

/-! Conserved linear identities of the actual arithmetic midpoint CF loop.
The initial numerator/denominator are reconstructed from the current
Euclidean pair and continuants. These identities cover the last rejected
convergent too, and bound actual constructed operands without an input-width
or bounded-continuant assumption.
-/
namespace Blotto.GeneralPaperCFLinearInvariant
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Linear (N M : ℕ) (s : State) : Prop :=
  N=s.numerator*s.previousNum+s.denominator*s.olderNum ∧
    M=s.numerator*s.previousDen+s.denominator*s.olderDen

theorem initial_linear (C t : ℕ) : Linear (2*t+1) (2*C) (initial C t) := by
  simp only [Linear,initial,Nat.mul_one,Nat.mul_zero,Nat.zero_add,Nat.add_zero,and_self]

theorem advance_linear (D width N M : ℕ) (s : State) (hPair : PairBound width s) (hLinear : Linear N M s) :
    Linear N M (advance D (width+2) s).1 := by
  by_cases hz : s.denominator=0
  · simpa only [advance,ite_eq_left hz,Linear] using hLinear
  · have hd : 0<s.denominator := by omega
    have he := (GeneralPaperConstructedNatDivision.run_spec s.numerator s.denominator (width+2) hd
      (quotient_cap width _ _ hPair.1 hd)).1
    have hN := hLinear.1
    have hM := hLinear.2
    have hn := congrArg (fun n : ℕ => n*s.previousNum) he
    have hm := congrArg (fun n : ℕ => n*s.previousDen) he
    simp only [advance,ite_eq_right hz]
    split
    · split <;> dsimp only [Linear] <;> constructor <;> nlinarith only [hN,hM,hn,hm]
    · dsimp only [Linear]
      constructor <;> nlinarith only [hN,hM,hn,hm]

theorem advance_numerator_positive (D divisionFuel : ℕ) (s : State) (hN : 0<s.numerator) :
    0<(advance D divisionFuel s).1.numerator := by
  by_cases hz : s.denominator=0
  · simpa only [advance,ite_eq_left hz] using hN
  · simp only [advance,ite_eq_right hz]
    split
    · split <;> dsimp only <;> omega
    · dsimp only
      omega

theorem run_linear (D width fuel N M : ℕ) (s : State) (hPair : PairBound width s) (hLinear : Linear N M s) :
    Linear N M (run D (width+2) fuel s) := by
  induction fuel generalizing s with
  | zero => exact hLinear
  | succ fuel ih =>
    have he := advance_linear D width N M s hPair hLinear
    dsimp only [run]
    split
    · exact ih _ (advance_pair_bound D width s hPair) he
    · exact he

theorem run_numerator_positive (D divisionFuel fuel : ℕ) (s : State) (hN : 0<s.numerator) :
    0<(run D divisionFuel fuel s).numerator := by
  induction fuel generalizing s with
  | zero => exact hN
  | succ fuel ih =>
    have he := advance_numerator_positive D divisionFuel s hN
    dsimp only [run]
    split
    · exact ih _ he
    · exact he

theorem previous_bounds (N M : ℕ) (s : State) (hLinear : Linear N M s) (hN : 0<s.numerator) :
    s.previousNum≤N ∧ s.previousDen≤M := by
  have hn : s.previousNum≤s.numerator*s.previousNum := by
    have he := Nat.mul_le_mul_right s.previousNum hN
    simpa only [Nat.one_mul] using he
  have hm : s.previousDen≤s.numerator*s.previousDen := by
    have he := Nat.mul_le_mul_right s.previousDen hN
    simpa only [Nat.one_mul] using he
  exact ⟨hn.trans (by rw [hLinear.1]; omega),hm.trans (by rw [hLinear.2]; omega)⟩

theorem midpoint_previous_bounds (D C t lambda fuel : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (run D (lambda+2) fuel (initial C t)).previousNum≤2*t+1 ∧
      (run D (lambda+2) fuel (initial C t)).previousDen≤2*C := by
  exact previous_bounds (2*t+1) (2*C) _
    (run_linear D lambda fuel _ _ _ (midpoint_pair_bound C t lambda hC ht hPower) (initial_linear C t))
    (run_numerator_positive D (lambda+2) fuel (initial C t) (by dsimp only [initial]; omega))

end Blotto.GeneralPaperCFLinearInvariant
