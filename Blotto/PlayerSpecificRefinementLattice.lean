import Blotto.PlayerSpecificCandidateSign

/-! General rational-interval midpoint lattices. Retained endpoints share
a positive denominator D; after k splits the denominator is D*2^k. This
prevents spurious exponential height growth from generic rational addition. -/
namespace Blotto.PlayerSpecificRefinementLattice
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 2000000

def OnLattice (q : ℚ) (D : ℕ) : Prop := ∃ a : ℤ,q=(a:ℚ)/(D:ℚ)
def Grid (node : Interval) (D : ℕ) : Prop := OnLattice node.lo D ∧ OnLattice node.hi D
def denominator (node : Interval) : ℕ := node.lo.den*node.hi.den

theorem denominator_positive (node : Interval) : 0<denominator node := Nat.mul_pos node.lo.den_pos node.hi.den_pos

theorem common_left (q r : ℚ) : OnLattice q (q.den*r.den) := by
  refine ⟨q.num*(r.den:ℤ),?_⟩
  calc
    q = (q.num:ℚ)/(q.den:ℚ) := q.num_div_den.symm
    _ = _ := by
      push_cast
      field_simp

theorem initial_grid (node : Interval) : Grid node (denominator node) := by
  refine ⟨common_left node.lo node.hi,?_⟩
  have h:=common_left node.hi node.lo
  simpa only [denominator,Nat.mul_comm] using h

theorem next (q : ℚ) (D : ℕ) (hD : 0<D) (hq : OnLattice q D) : OnLattice q (D*2) := by
  obtain ⟨a,ha⟩:=hq
  refine ⟨2*a,?_⟩
  rw [ha]
  push_cast
  field_simp

theorem midpoint (a b : ℚ) (D : ℕ) (hD : 0<D) (ha : OnLattice a D) (hb : OnLattice b D) :
    OnLattice ((a+b)/2) (D*2) := by
  obtain ⟨x,hx⟩:=ha
  obtain ⟨y,hy⟩:=hb
  refine ⟨x+y,?_⟩
  rw [hx,hy]
  push_cast
  field_simp

theorem split_grid {p : Data} (prepared : Prepared p) (node : Interval) (D : ℕ) (hD : 0<D) (hg : Grid node D) :
    Grid (split prepared node).1 (D*2) ∧ Grid (split prepared node).2 (D*2) :=
  ⟨⟨next _ D hD hg.1,midpoint _ _ D hD hg.1 hg.2⟩,
    ⟨midpoint _ _ D hD hg.1 hg.2,next _ D hD hg.2⟩⟩

theorem step_grid {p : Data} (prepared : Prepared p) (node : Interval) (D : ℕ) (hD : 0<D) (hg : Grid node D) :
    Grid (PlayerSpecificSelectedRefinement.step prepared node) (D*2) := by
  have hs:=split_grid prepared node D hD hg
  rw [PlayerSpecificSelectedRefinement.step]
  split
  · exact hs.1
  · exact hs.2

theorem run_grid {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (D : ℕ) (hD : 0<D) (hg : Grid node D) :
    Grid (PlayerSpecificSelectedRefinement.run prepared fuel node) (D*2^fuel) := by
  induction fuel generalizing node D with
  | zero => simpa only [PlayerSpecificSelectedRefinement.run,pow_zero,mul_one] using hg
  | succ fuel ih =>
    have hs:=ih (PlayerSpecificSelectedRefinement.step prepared node) (D*2) (by omega) (step_grid prepared node D hD hg)
    have he : D*2^(fuel+1)=(D*2)*2^fuel := by rw [pow_succ]; ring
    simpa only [PlayerSpecificSelectedRefinement.run,he] using hs

end Blotto.PlayerSpecificRefinementLattice
