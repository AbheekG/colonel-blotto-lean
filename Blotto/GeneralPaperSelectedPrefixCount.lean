import Blotto.GeneralPaperSelectedShift

/-! Exact midpoint-cell prefix counts. Each prefix has signed discrepancy
at most 1/(2S), with equality at a midpoint handled by the strict test. -/
namespace Blotto.GeneralPaperSelectedPrefixCount
open GeneralPaperSelectedShift
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def count (D S : ℕ) (hD : 0<D) (hS : 0<S) (A : ℕ) : ℕ :=
  (Finset.univ.filter (fun l:Fin S => (selected D S hD hS l).val<A)).card

theorem odd_test (D X l : ℕ) (hD : 0<D) :
    (2*l+1)*D<X ↔ l<(X+D-1)/(2*D) := by
  conv_rhs => rw [←Nat.succ_le_iff,Nat.le_div_iff_mul_le (by omega : 0<2*D)]
  have hs : X+D-1+1=X+D := by omega
  constructor <;> intro h <;> nlinarith only [hs,h]

theorem formula (D S : ℕ) (hD : 0<D) (hS : 0<S) (A : ℕ) :
    count D S hD hS A=min S ((2*S*A+D-1)/(2*D)) := by
  unfold count
  have he : Finset.univ.filter (fun l:Fin S => (selected D S hD hS l).val<A)=
      Finset.univ.filter (fun l:Fin S => l.val<(2*S*A+D-1)/(2*D)) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (selected_prefix D S hD hS l A).trans (odd_test D (2*S*A) l.val hD)
  rw [he,GeneralPaperQuantileRankCount.prefix_card]

theorem quotient_le (D S A : ℕ) (hD : 0<D) (hA : A≤D) : (2*S*A+D-1)/(2*D)≤S := by
  have h := Nat.mul_le_mul_left (2*S) hA
  have hs : 2*S*A+D-1+1=2*S*A+D := by omega
  have hlt : 2*S*A+D-1<(S+1)*(2*D) := by nlinarith only [h,hs,hD]
  have hq := (Nat.div_lt_iff_lt_mul (by omega : 0<2*D)).mpr hlt
  omega

theorem integer_bounds (D S : ℕ) (hD : 0<D) (hS : 0<S) (A : ℕ) (hA : A≤D) :
    2*S*A≤2*count D S hD hS A*D+D ∧ 2*count D S hD hS A*D≤2*S*A+D := by
  rw [formula,Nat.min_eq_right (quotient_le D S A hD hA)]
  let N := 2*S*A+D-1
  let q := N/(2*D)
  have hs : N+1=2*S*A+D := by dsimp only [N];omega
  have hr := Nat.mod_add_div N (2*D)
  change N%(2*D)+(2*D)*q=N at hr
  have hl := Nat.mod_lt N (by omega : 0<2*D)
  have hn : 0≤N%(2*D) := Nat.zero_le _
  change 2*S*A≤2*q*D+D ∧ 2*q*D≤2*S*A+D
  constructor <;> nlinarith only [hs,hr,hl,hn]

theorem probability_bounds (D S : ℕ) (hD : 0<D) (hS : 0<S) (A : ℕ) (hA : A≤D) :
    -(1/(2*(S:ℝ)))≤(count D S hD hS A:ℝ)/S-(A:ℝ)/D ∧
      (count D S hD hS A:ℝ)/S-(A:ℝ)/D≤1/(2*(S:ℝ)) := by
  have h := integer_bounds D S hD hS A hA
  have hl : (2:ℝ)*S*A≤2*(count D S hD hS A:ℝ)*D+D := by exact_mod_cast h.1
  have hu : (2:ℝ)*(count D S hD hS A)*D≤2*(S:ℝ)*A+D := by exact_mod_cast h.2
  have hd : (D:ℝ)≠0 := by exact_mod_cast hD.ne'
  have hs : (S:ℝ)≠0 := by exact_mod_cast hS.ne'
  have hp : (0:ℝ)<(2*S*D:ℕ) := by exact_mod_cast Nat.mul_pos (by omega : 0<2*S) hD
  have he : ((count D S hD hS A:ℝ)/S-(A:ℝ)/D)*(2*S*D:ℕ)=
      2*(count D S hD hS A:ℝ)*D-2*S*A := by push_cast;field_simp
  have hHalf : (1/(2*(S:ℝ)))*(2*S*D:ℕ)=(D:ℝ) := by push_cast;field_simp
  constructor
  · apply le_of_mul_le_mul_right (a:=((2*S*D:ℕ):ℝ)) ?_ hp
    rw [neg_mul,hHalf,he]
    linarith only [hl]
  · apply le_of_mul_le_mul_right (a:=((2*S*D:ℕ):ℝ)) ?_ hp
    rw [he,hHalf]
    linarith only [hu]

end Blotto.GeneralPaperSelectedPrefixCount
