import Blotto.PlayerSpecificLongDivisionHeights

/-! A fixed-degree linear rational-height bound for arbitrary computed
polynomial division, including normalization and inverse-leading scaling.
Both returned lists have stored length no greater than the dividend's. -/
namespace Blotto.PlayerSpecificDivisionHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 5000000

def height (H : ℕ) : ℕ := H+PlayerSpecificLongDivisionHeights.height 4 4 (2*H)+1

theorem height_ge (H : ℕ) : H≤height H := by unfold height; omega

theorem height_mono : Monotone height := by
  intro H J h
  exact Nat.add_le_add_right (Nat.add_le_add h (PlayerSpecificLongDivisionHeights.height_mono 4 4 (Nat.mul_le_mul_left 2 h))) 1

theorem linear (H : ℕ) : height H=32211*H+9666 := by
  rw [height,PlayerSpecificLongDivisionHeights.fixed_degree_linear]
  ring

theorem monicize_height (q : Data) (H : ℕ) (hq : HasHeight q H) (hH : 1≤H) :
    HasHeight (PlayerSpecificPolynomialDivision.monicize q) (2*H) := by
  have hi := (default_height hq hH).inv
  have h := trim_height (scale_height hi hq)
  simpa only [PlayerSpecificPolynomialDivision.monicize,PlayerSpecificPolynomialDivision.inverseLead,two_mul] using h

theorem monicize_length (q : Data) : (PlayerSpecificPolynomialDivision.monicize q).length≤q.length := by
  exact (trim_length _).trans (le_of_eq (scale_length _ _))

theorem run_height (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (PlayerSpecificPolynomialDivision.run p q).1 (height H) ∧
      HasHeight (PlayerSpecificPolynomialDivision.run p q).2 (height H) := by
  unfold PlayerSpecificPolynomialDivision.run
  dsimp only
  split
  · exact ⟨nil_height _,mono (trim_height hp) (height_ge H)⟩
  · have hqt := trim_height hq
    have hlen := (monicize_length (trim q)).trans ((trim_length q).trans hql)
    have htwo : 1≤2*H := by omega
    have hdiv := PlayerSpecificLongDivisionHeights.run_height p (PlayerSpecificPolynomialDivision.monicize (trim q))
      (2*H) (mono hp (by omega)) (monicize_height (trim q) H hqt hH) htwo hpl hlen
    constructor
    · exact mono (trim_height (scale_height (default_height hqt hH).inv hdiv.1)) (by unfold height; omega)
    · exact mono hdiv.2 (by unfold height; omega)

theorem quotient_length (p q : Data) : (PlayerSpecificPolynomialDivision.run p q).1.length≤p.length := by
  unfold PlayerSpecificPolynomialDivision.run
  dsimp only
  split
  · simp only [List.length_nil]; omega
  · rename_i hn
    have hm := PlayerSpecificPolynomialDivision.monicize_monic (trim q) (trim_normalized q) hn
    have h := PlayerSpecificCancellationHeights.monic_quotient_length _ p.length p (trim_normalized _) hm
    have ht := trim_length (scale (PlayerSpecificPolynomialDivision.inverseLead (trim q))
      (PlayerSpecificMonicDivision.run p (PlayerSpecificPolynomialDivision.monicize (trim q))).1)
    rw [scale_length] at ht
    exact ht.trans h

theorem remainder_length (p q : Data) : (PlayerSpecificPolynomialDivision.run p q).2.length≤p.length := by
  unfold PlayerSpecificPolynomialDivision.run
  dsimp only
  split
  · exact trim_length p
  · rename_i hn
    have hm := PlayerSpecificPolynomialDivision.monicize_monic (trim q) (trim_normalized q) hn
    exact PlayerSpecificCancellationHeights.monic_remainder_length _ p.length p (trim_normalized _) hm

end Blotto.PlayerSpecificDivisionHeights
