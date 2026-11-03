import Blotto.PlayerSpecificRefinementLattice

/-! Linear endpoint heights for arbitrary rational-interval refinement.
The common denominator is proof data; the executing source still stores
canonical rational endpoints and computes its actual midpoint normally. -/
namespace Blotto.PlayerSpecificRefinementEndpointHeights
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRefinementLattice
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem denominator_bound (node : Interval) : denominator node≤2^(2*PlayerSpecificSignEnclosure.endpointHeight node) := by
  let H:=PlayerSpecificSignEnclosure.endpointHeight node
  have hlo: RationalHeight node.lo H := PlayerSpecificRationalMagnitude.member_height [node.lo,node.hi] node.lo (by simp)
  have hhi: RationalHeight node.hi H := PlayerSpecificRationalMagnitude.member_height [node.lo,node.hi] node.hi (by simp)
  have hm:=Nat.mul_le_mul hlo.2.le hhi.2.le
  change denominator node≤2^H*2^H at hm
  rw [←pow_add] at hm
  simpa only [two_mul] using hm

theorem lattice_height (q : ℚ) (D k H : ℕ) (hD : 0<D) (hDb : D≤2^(2*H))
    (hg : OnLattice q (D*2^k)) (hb : |q| ≤ (2^H:ℕ)) : RationalHeight q (3*H+k+2) := by
  obtain ⟨a,ha⟩:=hg
  have hN : 0<D*2^k := Nat.mul_pos hD (Nat.two_pow_pos _)
  have hNQ : (0:ℚ)<(D*2^k:ℕ) := by exact_mod_cast hN
  have hab : (a.natAbs:ℚ)≤((2^H:ℕ):ℚ)*((D*2^k:ℕ):ℚ) := by
    rw [ha,abs_div,abs_of_pos hNQ] at hb
    have hh:=(div_le_iff₀ hNQ).mp hb
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  have habN : a.natAbs≤2^H*(D*2^k) := by exact_mod_cast hab
  have hden : D*2^k≤2^(2*H+k) := by rw [pow_add]; exact Nat.mul_le_mul_right _ hDb
  have hnum : a.natAbs≤2^(3*H+k) := by
    calc
      _ ≤ 2^H*(D*2^k) := habN
      _ ≤ 2^H*2^(2*H+k) := Nat.mul_le_mul_left _ hden
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hden' : D*2^k≤2^(3*H+k) := hden.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp:=Nat.two_pow_pos (3*H+k)
  rw [ha]
  apply RationalHeight.fraction a (D*2^k) _ hN
  · rw [show 3*H+k+2=(3*H+k)+2 by omega,pow_add]
    norm_num only [Nat.reducePow]
    omega
  · rw [show 3*H+k+2=(3*H+k)+2 by omega,pow_add]
    norm_num only [Nat.reducePow]
    omega

theorem step_bounded {p : Data} (prepared : Prepared p) (node : Interval) (M : ℚ)
    (hv : Valid prepared node) (hb : PlayerSpecificDyadicEndpoints.Bounded node M) :
    PlayerSpecificDyadicEndpoints.Bounded (PlayerSpecificSelectedRefinement.step prepared node) M := by
  have hs:=PlayerSpecificDyadicEndpoints.split_bounded prepared node M hv hb
  rw [PlayerSpecificSelectedRefinement.step]
  split
  · exact hs.1
  · exact hs.2

theorem run_bounded {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (M : ℚ)
    (hv : Valid prepared node) (hb : PlayerSpecificDyadicEndpoints.Bounded node M) :
    PlayerSpecificDyadicEndpoints.Bounded (PlayerSpecificSelectedRefinement.run prepared fuel node) M := by
  induction fuel generalizing node with
  | zero => exact hb
  | succ fuel ih =>
    exact ih (PlayerSpecificSelectedRefinement.step prepared node)
      (PlayerSpecificSelectedRefinement.step_valid prepared node hv) (step_bounded prepared node M hv hb)

theorem returned_heights {p : Data} (prepared : Prepared p) (node : Interval) (hv : node.lo<node.hi) (fuel : ℕ) :
    let result:=PlayerSpecificSelectedRefinement.run prepared fuel (PlayerSpecificSignEnclosure.retag prepared node)
    RationalHeight result.lo (3*PlayerSpecificSignEnclosure.endpointHeight node+fuel+2) ∧
      RationalHeight result.hi (3*PlayerSpecificSignEnclosure.endpointHeight node+fuel+2) := by
  let H:=PlayerSpecificSignEnclosure.endpointHeight node
  let M:ℚ:=(2^H:ℕ)
  let initial:=PlayerSpecificSignEnclosure.retag prepared node
  let result:=PlayerSpecificSelectedRefinement.run prepared fuel initial
  have hi : Valid prepared initial := PlayerSpecificSignEnclosure.initial_valid prepared node hv
  have hg : Grid result (denominator node*2^fuel) :=
    run_grid prepared fuel initial (denominator node) (denominator_positive node) (initial_grid node)
  have he:=PlayerSpecificSignEnclosure.endpoints node
  have hlo : -M≤node.lo := by
    have hh:=(abs_lt.mp he.1).1.le
    exact_mod_cast hh
  have hhi : node.hi≤M := by
    have hh:=(abs_lt.mp he.2).2.le
    exact_mod_cast hh
  have hb : PlayerSpecificDyadicEndpoints.Bounded result M := run_bounded prepared fuel initial M hi ⟨hlo,hhi⟩
  have hr : Valid prepared result := PlayerSpecificSelectedRefinement.run_valid prepared fuel initial hi
  have hablo : |result.lo| ≤ M := abs_le.mpr ⟨hb.1,hr.1.le.trans hb.2⟩
  have habhi : |result.hi| ≤ M := abs_le.mpr ⟨hb.1.trans hr.1.le,hb.2⟩
  exact ⟨lattice_height result.lo _ fuel H (denominator_positive node) (denominator_bound node) hg.1 hablo,
    lattice_height result.hi _ fuel H (denominator_positive node) (denominator_bound node) hg.2 habhi⟩

end Blotto.PlayerSpecificRefinementEndpointHeights
