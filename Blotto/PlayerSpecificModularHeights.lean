import Blotto.PlayerSpecificCandidateFieldInput

/-! A fixed-length modular Horner loop preserves linear coefficient sizes.
The geometric factor depends only on the at-most-seventeen coefficient
certificate length, never on the encoded input height. -/
namespace Blotto.PlayerSpecificModularHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificModularHorner
set_option autoImplicit false
set_option maxHeartbeats 3000000

def height (fuel H : ℕ) : ℕ := 1000000^fuel*(H+1)

theorem height_ge (fuel H : ℕ) : H+1≤height fuel H := by
  have hp : 1≤1000000^fuel := Nat.pow_pos (by decide)
  exact (by simpa only [height,one_mul] using Nat.mul_le_mul_right (H+1) hp)

theorem fuel_mono (H : ℕ) : Monotone (fun fuel => height fuel H) := by
  intro i j hij
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hij)

theorem input_height (c : ℚ) (b rest : Data) (H G : ℕ) (hc : RationalHeight c H)
    (hb : HasHeight b H) (hr : HasHeight rest G) (hHG : H+1≤G) :
    HasHeight (input c b rest) (4*G) := by
  have hi:=add_height (scale_height hc hb) (shift_height hr (by omega))
  exact mono hi (by omega)

theorem run_height (m b a : Data) (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4)
    (hbl : b.length≤3) (H : ℕ) (hmH : HasHeight m H) (hbH : HasHeight b H) (haH : HasHeight a H) :
    HasHeight (run m b a) (height a.length H) := by
  induction a with
  | nil => exact nil_height _
  | cons c cs ih =>
    have hg:=height_ge cs.length H
    have hi:=input_height c b (run m b cs) H (height cs.length H) (head_height haH) hbH (ih (tail_height haH)) hg
    have hl:=dividend_length m b hm hm0 hml hbl c cs
    have hd:=PlayerSpecificDivisionHeights.run_height (input c b (run m b cs)) m (4*height cs.length H)
      hi (mono hmH (by omega)) (by omega) hl hml
    apply mono hd.2
    rw [PlayerSpecificDivisionHeights.linear,List.length_cons]
    unfold height
    rw [pow_succ]
    change 32211*(4*(1000000^cs.length*(H+1)))+9666≤
      (1000000^cs.length*1000000)*(H+1)
    change H+1≤1000000^cs.length*(H+1) at hg
    nlinarith only [hg]

end Blotto.PlayerSpecificModularHeights
