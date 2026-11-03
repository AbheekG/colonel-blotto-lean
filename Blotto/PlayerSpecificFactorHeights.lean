import Blotto.PlayerSpecificRationalFactors

/-! Rational-factor removal has a constant number of affine coefficient
growth steps. The bounds follow the actual recovered root and actual quotient. -/
namespace Blotto.PlayerSpecificFactorHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude
open PlayerSpecificLinearFactor
set_option autoImplicit false
set_option maxHeartbeats 3000000

def step (H : ℕ) : ℕ := 2000000*(H+1)
def height : ℕ → ℕ → ℕ
  | 0,H => H
  | fuel+1,H => height fuel (step H)

theorem step_ge (H : ℕ) : H≤step H := by unfold step; omega
theorem height_ge (fuel H : ℕ) : H≤height fuel H := by
  induction fuel generalizing H with
  | zero => rfl
  | succ fuel ih => exact (step_ge H).trans (ih (step H))

theorem input_bound (p : Data) (H : ℕ) (hp : HasHeight p H) (hlen : p.length≤4) : inputHeight p≤8*H+5 := by
  have hi:=inputHeight_le hp
  have hm:=Nat.mul_le_mul_right (1+2*H) hlen
  omega

theorem recovered_height (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (H : ℕ) (hH : HasHeight p H) (q : ℚ) (hq : evaluate p q=0) : RationalHeight q (56*H+37) := by
  have hr:=PlayerSpecificRationalRootHeight.root_height p hp hlen q hq
  exact hr.mono (by have hi:=input_bound p H hH hlen; unfold PlayerSpecificRationalRootHeight.height; omega)

theorem linear_height (q : ℚ) (H : ℕ) (hq : RationalHeight q H) (hH : 1≤H) : HasHeight (linear q) H :=
  cons_height hq.neg (cons_height (one_height.mono hH) (nil_height H))

theorem quotient_height (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (H : ℕ) (hH : HasHeight p H) (q : ℚ) (hq : evaluate p q=0) : HasHeight (quotient p q) (step H) := by
  have hr:=recovered_height p hp hlen H hH q hq
  have hu : H≤56*H+37 := by omega
  have hh:=PlayerSpecificDivisionHeights.run_height p (linear q) (56*H+37)
    (mono hH hu) (linear_height q _ hr (by omega)) (by omega) hlen (by simp only [linear,List.length_cons,List.length_nil]; decide)
  apply mono hh.1
  rw [PlayerSpecificDivisionHeights.linear]
  unfold step
  omega

theorem run_height (fuel : ℕ) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (hfuel : p.length≤fuel) (H : ℕ) (hH : HasHeight p H) :
    HasHeight (PlayerSpecificRationalFactors.run fuel p).1 (height fuel H) ∧
      HasHeight (PlayerSpecificRationalFactors.run fuel p).2 (height fuel H) := by
  induction fuel generalizing p H with
  | zero => exact ⟨nil_height H,trim_height hH⟩
  | succ fuel ih =>
    cases hr : PlayerSpecificRationalRoots.run p with
    | nil =>
      simp only [PlayerSpecificRationalFactors.run,hr]
      exact ⟨nil_height _,mono (trim_height hH) (height_ge (fuel+1) H)⟩
    | cons q qs =>
      have hq:=PlayerSpecificRationalRoots.sound p q (by rw [hr]; exact List.mem_cons_self)
      have hd:=length_drop p hp q hq
      have hh:=ih (quotient p q) (quotient_nonzero p hp q hq) (by omega) (by omega)
        (step H) (quotient_height p hp hlen H hH q hq)
      simp only [PlayerSpecificRationalFactors.run,hr,height]
      refine ⟨cons_height ?_ hh.1,hh.2⟩
      exact (recovered_height p hp hlen H hH q hq).mono
        ((show 56*H+37≤step H by unfold step; omega).trans (height_ge fuel (step H)))

theorem linear_bound (fuel H : ℕ) : height fuel H≤4000000^fuel*(H+1) := by
  induction fuel generalizing H with
  | zero => simp only [height,pow_zero,one_mul]; omega
  | succ fuel ih =>
    have hh:=ih (step H)
    have hs : step H+1≤4000000*(H+1) := by unfold step; omega
    have hm:=Nat.mul_le_mul_left (4000000^fuel) hs
    rw [height,pow_succ]
    exact hh.trans (hm.trans_eq (by ring))

end Blotto.PlayerSpecificFactorHeights
