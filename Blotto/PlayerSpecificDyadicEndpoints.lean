import Blotto.PlayerSpecificIsolationDepthHeight

/-! Actual bisection endpoints lie on dyadic grids. Their reduced rational
heights grow linearly with the initial enclosure exponent and traversal
depth, including cancellations and exact rational roots at midpoints. -/
namespace Blotto.PlayerSpecificDyadicEndpoints
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
open PlayerSpecificRootMagnitude
set_option autoImplicit false
set_option maxHeartbeats 600000

def OnGrid (q : ℚ) (k : ℕ) : Prop := ∃ a : ℤ,q=(a:ℚ)/(2:ℚ)^k

theorem grid_next (q : ℚ) (k : ℕ) (h : OnGrid q k) : OnGrid q (k+1) := by
  obtain ⟨a,ha⟩ := h
  refine ⟨2*a,?_⟩
  rw [ha,pow_succ]
  push_cast
  field_simp

theorem grid_midpoint (a b : ℚ) (k : ℕ) (ha : OnGrid a k) (hb : OnGrid b k) : OnGrid ((a+b)/2) (k+1) := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  refine ⟨x+y,?_⟩
  rw [hx,hy,pow_succ]
  push_cast
  field_simp

theorem grid_height (p : Data) (q : ℚ) (k : ℕ) (hg : OnGrid q k) (hb : |q| ≤ (rootBound p:ℚ)) :
    RationalHeight q (2*inputHeight p+k+4) := by
  obtain ⟨a,ha⟩ := hg
  have hpow : (0:ℚ)<(2:ℚ)^k := pow_pos (by norm_num) _
  have hn : (a.natAbs:ℚ)≤(rootBound p:ℚ)*(2:ℚ)^k := by
    have hab : |(a:ℚ)|≤(rootBound p:ℚ)*(2:ℚ)^k := by
      rw [ha,abs_div,abs_of_pos hpow] at hb
      exact (div_le_iff₀ hpow).mp hb
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hab
  have hnat : a.natAbs≤rootBound p*2^k := by exact_mod_cast hn
  rw [rootBound,← pow_add] at hnat
  have hd : 2^k≤2^(2*inputHeight p+2+k) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := Nat.two_pow_pos (2*inputHeight p+2+k)
  rw [ha]
  have he : (2:ℚ)^k=((2^k:ℕ):ℚ) := by norm_cast
  rw [he]
  apply RationalHeight.fraction a (2^k) _ (Nat.two_pow_pos _)
  · rw [show 2*inputHeight p+k+4=(2*inputHeight p+2+k)+2 by omega,pow_add]
    norm_num only [Nat.reducePow]
    omega
  · rw [show 2*inputHeight p+k+4=(2*inputHeight p+2+k)+2 by omega,pow_add]
    norm_num only [Nat.reducePow]
    omega

def Grid (node : Interval) (k : ℕ) : Prop := OnGrid node.lo k ∧ OnGrid node.hi k
def Bounded (node : Interval) (M : ℚ) : Prop := -M≤node.lo ∧ node.hi≤M

theorem endpoint_height (p : Data) (prepared : Prepared p) (node : Interval) (k : ℕ)
    (hv : Valid prepared node) (hg : Grid node k) (hb : Bounded node (rootBound p:ℚ)) :
    RationalHeight node.lo (2*inputHeight p+k+4) ∧ RationalHeight node.hi (2*inputHeight p+k+4) := by
  have hlo : |node.lo| ≤ (rootBound p:ℚ) := abs_le.mpr ⟨hb.1,hv.1.le.trans hb.2⟩
  have hhi : |node.hi| ≤ (rootBound p:ℚ) := abs_le.mpr ⟨hb.1.trans hv.1.le,hb.2⟩
  exact ⟨grid_height p node.lo k hg.1 hlo,grid_height p node.hi k hg.2 hhi⟩

theorem split_grid {p : Data} (prepared : Prepared p) (node : Interval) (k : ℕ) (h : Grid node k) :
    Grid (split prepared node).1 (k+1) ∧ Grid (split prepared node).2 (k+1) :=
  ⟨⟨grid_next _ _ h.1,grid_midpoint _ _ k h.1 h.2⟩,
    ⟨grid_midpoint _ _ k h.1 h.2,grid_next _ _ h.2⟩⟩

theorem split_bounded {p : Data} (prepared : Prepared p) (node : Interval) (M : ℚ)
    (h : Valid prepared node) (hb : Bounded node M) :
    Bounded (split prepared node).1 M ∧ Bounded (split prepared node).2 M := by
  have hm := midpoint_between node h.1
  exact ⟨⟨hb.1,hm.2.le.trans hb.2⟩,⟨hb.1.trans hm.1.le,hb.2⟩⟩

theorem forest_grid {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (k : ℕ) (h : Grid node k) :
    ∀ leaf∈PlayerSpecificIsolationForest.run prepared fuel node,Grid leaf (k+fuel) := by
  induction fuel generalizing node k with
  | zero =>
    rw [PlayerSpecificIsolationForest.run]
    split
    · intro leaf hl; cases hl
    · intro leaf hl
      have he := List.mem_singleton.mp hl
      simpa only [he,Nat.add_zero] using h
  | succ fuel ih =>
    rw [PlayerSpecificIsolationForest.run]
    split
    · intro leaf hl; cases hl
    · have hg := split_grid prepared node k h
      intro leaf hl
      rcases List.mem_append.mp hl with hl | hr
      · simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using ih (split prepared node).1 (k+1) hg.1 leaf hl
      · simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using ih (split prepared node).2 (k+1) hg.2 leaf hr

theorem forest_bounded {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (M : ℚ)
    (h : Valid prepared node) (hb : Bounded node M) :
    ∀ leaf∈PlayerSpecificIsolationForest.run prepared fuel node,Bounded leaf M := by
  induction fuel generalizing node with
  | zero =>
    rw [PlayerSpecificIsolationForest.run]
    split
    · intro leaf hl; cases hl
    · intro leaf hl
      have he := List.mem_singleton.mp hl
      simpa only [he] using hb
  | succ fuel ih =>
    rw [PlayerSpecificIsolationForest.run]
    split
    · intro leaf hl; cases hl
    · have hg := split_bounded prepared node M h hb
      have hv := split_valid prepared node h
      intro leaf hl
      rcases List.mem_append.mp hl with hl | hr
      · exact ih (split prepared node).1 hv.1 hg.1 leaf hl
      · exact ih (split prepared node).2 hv.2 hg.2 leaf hr

theorem initial_grid (p : Data) (prepared : Prepared p) : Grid (initial p prepared) 0 := by
  refine ⟨⟨-(rootBound p:ℤ),?_⟩,⟨(rootBound p:ℤ),?_⟩⟩ <;>
    simp only [PlayerSpecificRootMagnitude.initial,PlayerSpecificIsolationState.initial,pow_zero,div_one,Int.cast_neg,Int.cast_natCast]

theorem initial_bounded (p : Data) (prepared : Prepared p) : Bounded (initial p prepared) (rootBound p:ℚ) :=
  ⟨le_rfl,le_rfl⟩

theorem returned_height (p : Data) (leaf : Interval) (hl : leaf∈PlayerSpecificRootIsolation.run p) :
    RationalHeight leaf.lo (2*inputHeight p+PlayerSpecificRootIsolation.depth p+4) ∧
      RationalHeight leaf.hi (2*inputHeight p+PlayerSpecificRootIsolation.depth p+4) := by
  have hg := forest_grid (prepare p) (PlayerSpecificRootIsolation.depth p) _ 0 (initial_grid p (prepare p)) leaf hl
  simp only [Nat.zero_add] at hg
  have hb := forest_bounded (prepare p) (PlayerSpecificRootIsolation.depth p) _ (rootBound p:ℚ)
    (initial_valid p (prepare p)) (initial_bounded p (prepare p)) leaf hl
  have hv := (PlayerSpecificRootIsolation.valid_positive p leaf hl).1
  exact endpoint_height p (prepare p) leaf _ hv hg hb

theorem returned_height_linear (p : Data) (hlen : p.length≤4) (leaf : Interval)
    (hl : leaf∈PlayerSpecificRootIsolation.run p) :
    RationalHeight leaf.lo ((PlayerSpecificIsolationDepthHeight.linearConstant+6)*(inputHeight p+1)) ∧
      RationalHeight leaf.hi ((PlayerSpecificIsolationDepthHeight.linearConstant+6)*(inputHeight p+1)) := by
  have h := returned_height p leaf hl
  have hd := PlayerSpecificIsolationDepthHeight.depth_linear p hlen
  have hm : 2*inputHeight p+PlayerSpecificRootIsolation.depth p+4≤
      (PlayerSpecificIsolationDepthHeight.linearConstant+6)*(inputHeight p+1) := by nlinarith
  exact ⟨h.1.mono hm,h.2.mono hm⟩

end Blotto.PlayerSpecificDyadicEndpoints
