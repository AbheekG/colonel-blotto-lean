import Blotto.PlayerSpecificPolynomialHeights

/-! Rational height bounds for actual monomial construction and leading-term
cancellation, together with stored-length bounds used by long division. -/
namespace Blotto.PlayerSpecificCancellationHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialCancellation
open PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem monomial_length (n : ℕ) (a : ℚ) : (monomial n a).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [monomial,List.length_cons,ih]

theorem monomial_height (n : ℕ) (a : ℚ) (s : ℕ) (ha : RationalHeight a s) (hs : 1≤s) :
    HasHeight (monomial n a) s := by
  induction n with
  | zero => exact cons_height ha (nil_height s)
  | succ n ih => exact cons_height (zero_height.mono hs) ih

theorem term_height (p q : Data) (s : ℕ) (hp : HasHeight p s) (hs : 1≤s) : HasHeight (term p q) s :=
  monomial_height _ _ s (default_height hp hs) hs

theorem term_length (p q : Data) (hp : p≠[]) (hq : q≠[]) : (term p q).length≤p.length := by
  rw [term,monomial_length]
  have h := List.length_pos_iff.mpr hq
  have h' := List.length_pos_iff.mpr hp
  omega

theorem remainder_height (p q : Data) (s t N : ℕ) (hp : HasHeight p s) (hq : HasHeight q t)
    (hs : 1≤s) (hlen : q.length≤N) :
    HasHeight (remainder p q) (s+(t+s+1)*(N+1)+1) := by
  apply trim_height
  apply mono (subtract_height hp (multiply_height hq (term_height p q s hp hs)))
  have hm := Nat.mul_le_mul_left (t+s+1) (Nat.add_le_add_right hlen 1)
  omega

theorem monic_quotient_length (q : Data) (fuel : ℕ) (p : Data) (hq : Normalized q)
    (hm : (semantics q).Monic) : (PlayerSpecificMonicDivision.loop q fuel p).1.length≤p.length := by
  have hq0 : q≠[] := by intro hz; apply hm.ne_zero; rw [hz]; rfl
  induction fuel generalizing p with
  | zero => simp only [PlayerSpecificMonicDivision.loop,List.length_nil]; omega
  | succ fuel ih =>
    rw [PlayerSpecificMonicDivision.loop]
    split
    · simp only [List.length_nil]; omega
    · rename_i hgo
      have hd := drops_length (trim p) q (trim_normalized p) hq (not_or.mp hgo).1 hm
        (le_of_not_gt (not_or.mp hgo).2)
      have ht := term_length (trim p) q (not_or.mp hgo).1 hq0
      have hi := ih (remainder (trim p) q)
      have hl := trim_length p
      have ho := trim_length (add (term (trim p) q)
        (PlayerSpecificMonicDivision.loop q fuel (remainder (trim p) q)).1)
      rw [add_length] at ho
      exact ho.trans ((max_le ht (hi.trans hd.le)).trans hl)

theorem monic_remainder_length (q : Data) (fuel : ℕ) (p : Data) (hq : Normalized q)
    (hm : (semantics q).Monic) : (PlayerSpecificMonicDivision.loop q fuel p).2.length≤p.length := by
  induction fuel generalizing p with
  | zero => exact trim_length p
  | succ fuel ih =>
    rw [PlayerSpecificMonicDivision.loop]
    split
    · exact trim_length p
    · rename_i hgo
      have hd := drops_length (trim p) q (trim_normalized p) hq (not_or.mp hgo).1 hm
        (le_of_not_gt (not_or.mp hgo).2)
      exact (ih _).trans (hd.le.trans (trim_length p))

end Blotto.PlayerSpecificCancellationHeights
