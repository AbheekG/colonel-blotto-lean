import Blotto.GeneralPaperInitializerParameters

/-! Executed downward N-grid rounding of unit anchors. The actual bounded
quotient implements the floor specification, including the endpoint one.
Order, zero, hard coordinate bounds, common lattice and strict whole-tuple
loss follow from that execution. No floor oracle is supplied.
-/
namespace Blotto.GeneralPaperInitializerRounding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  value : ℚ
  work : ℕ

def run (N depth : ℕ) (u : ℚ) : Result :=
  let q := GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth
  ⟨(q.quotient:ℚ)/N,q.work+16⟩

theorem value_floor (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) (u : ℚ) (hu : 0≤u ∧ u≤1) :
    (run N depth u).value=(⌊u*(N:ℚ)⌋₊:ℚ)/N := by
  have hn : (0:ℚ)<N := by exact_mod_cast hN
  have hc : u*(N:ℚ)<(2:ℚ)^depth := by
    have hh : (N:ℚ)<(2:ℚ)^depth := by exact_mod_cast hCap
    nlinarith only [hu.2,hn,hh]
  change ((GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth).quotient:ℚ)/N=_
  rw [GeneralPaperBoundedQuotient.run_floor _ depth (mul_nonneg hu.1 hn.le) hc]

theorem bounds (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) (u : ℚ) (hu : 0≤u ∧ u≤1) :
    0≤(run N depth u).value ∧ (run N depth u).value≤u ∧ u<(run N depth u).value+1/(N:ℚ) := by
  have hn : (0:ℚ)<N := by exact_mod_cast hN
  rw [value_floor N depth hN hCap u hu]
  have hl := Nat.floor_le (mul_nonneg hu.1 hn.le)
  have hh := Nat.lt_floor_add_one (u*(N:ℚ))
  refine ⟨by positivity,(div_le_iff₀ hn).mpr hl,?_⟩
  rw [←add_div]
  exact (lt_div_iff₀ hn).mpr hh

theorem zero (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) : (run N depth 0).value=0 := by
  rw [value_floor N depth hN hCap 0 (by norm_num)]
  norm_num

theorem monotone (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) (u v : ℚ)
    (hu : 0≤u ∧ u≤1) (hv : 0≤v ∧ v≤1) (huv : u≤v) : (run N depth u).value≤(run N depth v).value := by
  rw [value_floor N depth hN hCap u hu,value_floor N depth hN hCap v hv]
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast hN.le)
  exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_right huv (show (0:ℚ)≤N by positivity))

theorem lattice (N depth : ℕ) (hN : 0<N) (u : ℚ) : OnRationalLattice N (run N depth u).value := by
  have hn : (N:ℤ)≠0 := by exact_mod_cast hN.ne'
  have hd := FinitePolytopeRationalWitness.denominator_divInt
    (numerator:=((GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth).quotient:ℤ)) hn
  simpa only [run,OnRationalLattice,Int.cast_natCast,Int.natAbs_natCast] using hd

theorem tuple_loss {m : ℕ} (hm : 0<m) (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (u : Fin m → ℚ) (hu : ∀ j,0≤u j ∧ u j≤1) :
    (∑ j,u j)-(m:ℚ)/N<∑ j,(run N depth (u j)).value := by
  have hs := Finset.sum_lt_sum (s:=Finset.univ)
    (fun j _ => (bounds N depth hN hCap (u j) (hu j)).2.2.le)
    ⟨⟨0,hm⟩,Finset.mem_univ _,(bounds N depth hN hCap (u ⟨0,hm⟩) (hu ⟨0,hm⟩)).2.2⟩
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one_div] at hs
  linarith only [hs]

theorem run_work (N depth : ℕ) (u : ℚ) : (run N depth u).work=12*depth+18 := by
  change (GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth).work+16=_
  rw [GeneralPaperBoundedQuotient.run_work]

end Blotto.GeneralPaperInitializerRounding
