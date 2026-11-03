import Blotto.GeneralPaperCFRetention

/-! The actual midpoint loop first accepts 0/1. Its ensuing state has the
positive denominator, Euclidean order, selected fraction and conserved data
required by the retention theorem. All facts are derived from the executed
first step and the constructed midpoint controls.
-/
namespace Blotto.GeneralPaperCFFirstTerm
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFLinearInvariant
open GeneralPaperCFDeterminant GeneralPaperCFAdvanceData GeneralPaperCFError
set_option autoImplicit false
set_option maxHeartbeats 2500000

def first (D C t lambda : ℕ) : State := (advance D (lambda+2) (initial C t)).1

theorem quotient_zero (C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (GeneralPaperConstructedNatDivision.run (2*t+1) (2*C) (lambda+2)).quotient=0 := by
  have hd : 0<2*C := by omega
  have hp := midpoint_pair_bound C t lambda hC ht hPower
  have hn : 2*t+1<2^lambda := hp.1
  have hc := quotient_cap lambda (2*t+1) (2*C) hn hd
  rw [GeneralPaperConstructedNatDivision.quotient_eq (2*t+1) (2*C) (lambda+2) hd hc]
  exact Nat.div_eq_of_lt (by omega)

theorem first_more (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (advance D (lambda+2) (initial C t)).2=true := by
  have hq := quotient_zero C t lambda hC ht hPower
  have hd : 2*C≠0 := by omega
  have hD' : 1≤D := by omega
  simp [advance,initial,hq,hd,hD']

theorem first_fields (D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (first D C t lambda).previousNum=0 ∧ (first D C t lambda).previousDen=1 ∧
      (first D C t lambda).olderNum=1 ∧ (first D C t lambda).olderDen=0 := by
  have he := continuants D (lambda+2) (initial C t) (by dsimp only [initial]; omega)
  have hq := quotient_zero C t lambda hC ht hPower
  simp only [initial,hq,Nat.zero_mul,Nat.mul_one,Nat.zero_add,Nat.add_zero] at he
  exact ⟨he.2.2.1,he.2.2.2,he.1,he.2.1⟩

theorem first_post (D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    Post (2*t+1) (2*C) lambda (first D C t lambda) := by
  have hp := midpoint_pair_bound C t lambda hC ht hPower
  have hd : 0<(initial C t).denominator := by dsimp only [initial]; omega
  have he := advance_euclidean D (lambda+2) (initial C t) hd (quotient_cap lambda _ _ hp.1 hd)
  refine ⟨advance_pair_bound D lambda _ hp,advance_linear D lambda _ _ _ hp (initial_linear C t),
    advance_unimodular D (lambda+2) _ (initial_unimodular C t),?_,?_⟩
  · change (advance D (lambda+2) (initial C t)).1.denominator≤(advance D (lambda+2) (initial C t)).1.numerator
    rw [he.1,he.2]
    exact (Nat.mod_lt _ hd).le
  · rw [(first_fields D C t lambda hC ht hPower).2.1]
    exact Nat.zero_lt_one

theorem first_selected (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    CurrentSelected (first D C t lambda) := continuing_selection D (lambda+2) _ (first_more D C t lambda hD hC ht hPower)

theorem first_view (D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    GeneralPaperCFModel.view (first D C t lambda)=
      GeneralPaperCFModel.step (GeneralPaperCFModel.initial (2*t+1) (2*C)) :=
  GeneralPaperCFModel.advance_view D lambda (initial C t) (midpoint_pair_bound C t lambda hC ht hPower)

theorem first_stops (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    Stops D (lambda+2) (2*lambda+3) (first D C t lambda) := by
  have he := midpoint_stops D C t lambda hC ht hPower
  change (advance D (lambda+2) (initial C t)).2=false ∨ Stops D (lambda+2) (2*lambda+3) (first D C t lambda) at he
  exact he.elim (fun hBad => by rw [first_more D C t lambda hD hC ht hPower] at hBad; cases hBad) id

theorem raw_first (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    GeneralPaperMidpointQuery.raw D C t lambda=run D (lambda+2) (2*lambda+3) (first D C t lambda) := by
  change (if (advance D (lambda+2) (initial C t)).2 then
    run D (lambda+2) (2*lambda+3) (first D C t lambda) else first D C t lambda)=_
  simp only [first_more D C t lambda hD hC ht hPower,ite_true]

end Blotto.GeneralPaperCFFirstTerm
