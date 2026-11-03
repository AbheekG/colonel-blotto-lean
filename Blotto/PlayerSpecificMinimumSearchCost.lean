import Blotto.PlayerSpecificMinimumTestCost

/-! All halving-search work, including rational halves and enclosing
control/return copies, is bounded for the actual finite guard. -/
namespace Blotto.PlayerSpecificMinimumSearchCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificSturmVariations PlayerSpecificRationalTrace PlayerSpecificIsolationState
open PlayerSpecificMinimumSearch PlayerSpecificPositiveFieldLowerBound PlayerSpecificMinimumTestCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := scanCoefficient+1000

theorem dyadic_height (s : ℕ) : RationalHeight (dyadic s) (s+1) := by
  have hden : (2:ℕ)^s<2^(s+1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self s)
  have hnum : (1:ℤ).natAbs<2^(s+1) := by
    have hpow : 1≤(2:ℕ)^s := Nat.one_le_two_pow
    norm_num only [Int.natAbs_one]
    omega
  have h:=RationalHeight.fraction 1 (2^s) (s+1) (Nat.two_pow_pos s) hnum hden
  simpa only [dyadic,Int.cast_one,Nat.cast_pow,Nat.cast_ofNat] using h

theorem metadata (model : RationalCostModel) (m : Data) (node : Interval) (rows : List Data) (fuel s : ℕ) (q : ℚ)
    (hq : q=dyadic s) :
    let result:=search model m node rows fuel s q
    result.quantum=dyadic result.exponent ∧ s≤result.exponent ∧ result.exponent≤s+fuel ∧ result.checks≤fuel+1 := by
  induction fuel generalizing s q with
  | zero => simp only [search]; exact ⟨hq,le_rfl,by omega,le_rfl⟩
  | succ fuel ih =>
    simp only [search]
    split
    · dsimp only; exact ⟨hq,le_rfl,by omega,by omega⟩
    · have hh : (scalar .divide q 2).1=dyadic (s+1) := by simp only [scalar,Arithmetic.apply,hq,dyadic_succ]
      have hn:=ih (s+1) _ hh
      dsimp only
      exact ⟨hn.1,by omega,by omega,by omega⟩

theorem frame_cost (model : RationalCostModel) (rows : List Data) (fuel s H : ℕ) (q : ℚ)
    (hq : RationalHeight q H) (hr : rows.length≤H) (hf : fuel≤H) (hs : s≤H) :
    price model (frame rows fuel s q)≤100*model.rat (width H) := by
  have hcopy:=row_copy model [q] H (cons_height hq (nil_height H)) (by simp)
  have ha:=control model rows.length H (by omega)
  have hb:=control model fuel H (by omega)
  have hc:=control model s H (by omega)
  simp only [frame,price,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  omega

theorem result_copy (model : RationalCostModel) (q : ℚ) (s k H : ℕ) (hq : RationalHeight q H)
    (hs : s≤H) (hk : k≤H) :
    price model (copyRow [q]++[.control s,.control k])≤100*model.rat (width H) := by
  have hcopy:=row_copy model [q] H (cons_height hq (nil_height H)) (by simp)
  have ha:=control model s H (by omega)
  have hb:=control model k H (by omega)
  simp only [price,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  omega

theorem half_cost (model : RationalCostModel) (q : ℚ) (H : ℕ) (hq : RationalHeight q H) (hH : 2≤H) :
    price model (scalar .divide q 2).2≤15*model.rat (width H) := by
  have htwo : RationalHeight (2:ℚ) H := (show RationalHeight (2:ℚ) 2 by norm_num [RationalHeight]).mono hH
  have hf:=fits_mono (scalar_fits_height .divide q 2 H hq htwo)
    (show 4*H+3≤width H by have hw:=width_large H; omega)
  simpa only [scalar_length] using price_bound model (width H) (by have hw:=width_large H; omega) _ hf

theorem source_cost (model : RationalCostModel) (m : Data) (node : Interval) (rows : List Data)
    (fuel s H : ℕ) (q : ℚ) (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4)
    (hmH : HasHeight m H) (he : HasHeight [node.lo,node.hi] H) (hv : node.lo<node.hi)
    (hlen : rows.length≤H) (hrows : ∀ a∈rows,HasHeight a H ∧ a.length≤3)
    (hq : q=dyadic s) (hbudget : s+fuel+2≤H) :
    (search model m node rows fuel s q).work≤
      (fuel+1)*coefficient*(rows.length+1)*(H+1)*model.rat (width H) := by
  have hunit : model.rat (width H)≤(rows.length+1)*(H+1)*model.rat (width H) := by
    have hp : 1≤(rows.length+1)*(H+1) := Nat.mul_le_mul (by omega : 1≤rows.length+1) (by omega : 1≤H+1)
    simpa only [one_mul] using Nat.mul_le_mul_right (model.rat (width H)) hp
  induction fuel generalizing s q with
  | zero =>
    have hqh : RationalHeight q H := hq.symm ▸ (dyadic_height s).mono (by omega)
    have ht:=scan_cost model m node q rows H hm hm0 hml hmH he hqh (by omega) hv hlen hrows
    have hf:=frame_cost model rows 0 s H q hqh hlen (by omega) (by omega)
    simp only [search]
    unfold coefficient
    nlinarith only [ht,hf,hunit]
  | succ fuel ih =>
    have hqh : RationalHeight q H := hq.symm ▸ (dyadic_height s).mono (by omega)
    have ht:=scan_cost model m node q rows H hm hm0 hml hmH he hqh (by omega) hv hlen hrows
    have hf:=frame_cost model rows (fuel+1) s H q hqh hlen (by omega) (by omega)
    simp only [search]
    split
    · dsimp only
      have hc:=Nat.mul_le_mul_right (coefficient*(rows.length+1)*(H+1)*model.rat (width H))
        (show 1≤fuel+1+1 by omega)
      unfold coefficient at hc ⊢
      nlinarith only [ht,hf,hunit,hc]
    · have hh : (scalar .divide q 2).1=dyadic (s+1) := by simp only [scalar,Arithmetic.apply,hq,dyadic_succ]
      have hn:=ih (s+1) (scalar .divide q 2).1 hh (by omega)
      have hmdata:=metadata model m node rows fuel (s+1) (scalar .divide q 2).1 hh
      have hnext : RationalHeight (search model m node rows fuel (s+1) (scalar .divide q 2).1).quantum H :=
        hmdata.1.symm ▸ (dyadic_height _).mono (by omega)
      have hc:=result_copy model
        (search model m node rows fuel (s+1) (scalar .divide q 2).1).quantum
        (search model m node rows fuel (s+1) (scalar .divide q 2).1).exponent
        (search model m node rows fuel (s+1) (scalar .divide q 2).1).checks H hnext (by omega) (by omega)
      have hhCost:=half_cost model q H hqh (by omega)
      dsimp only
      unfold coefficient at hn ⊢
      nlinarith only [ht,hf,hn,hc,hhCost,hunit]

end Blotto.PlayerSpecificMinimumSearchCost
