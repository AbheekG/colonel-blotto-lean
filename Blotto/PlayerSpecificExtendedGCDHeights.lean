import Blotto.PlayerSpecificDivisionHeights

/-! Coefficient-height and stored-length bounds for the executed extended
Euclidean algorithm in degree at most three. The fuel is bounded from the
actual input length. The resulting height is affine in the input height. -/
namespace Blotto.PlayerSpecificExtendedGCDHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificExtendedGCD
set_option autoImplicit false
set_option maxHeartbeats 6000000

def height : ℕ → ℕ → ℕ
  | 0,H => H+1
  | fuel+1,H => 6*(PlayerSpecificDivisionHeights.height H+height fuel (PlayerSpecificDivisionHeights.height H)+1)

def affine : ℕ → ℕ×ℕ
  | 0 => (1,1)
  | fuel+1 => (6*32211*((affine fuel).1+1),6*(((affine fuel).1+1)*9666+(affine fuel).2+1))

theorem height_affine (fuel H : ℕ) : height fuel H=(affine fuel).1*H+(affine fuel).2 := by
  induction fuel generalizing H with
  | zero => simp only [height,affine,one_mul]
  | succ fuel ih => rw [height,ih,PlayerSpecificDivisionHeights.linear,affine]; ring

theorem height_mono (fuel : ℕ) : Monotone (height fuel) := by
  intro H J h
  rw [height_affine,height_affine]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

theorem height_ge (fuel H : ℕ) : H≤height fuel H := by
  induction fuel generalizing H with
  | zero => simp only [height]; omega
  | succ fuel ih =>
    have hd := PlayerSpecificDivisionHeights.height_ge H
    have ht := ih (PlayerSpecificDivisionHeights.height H)
    rw [height]
    omega

theorem fuel_mono (H : ℕ) : Monotone (fun fuel => height fuel H) := by
  apply monotone_nat_of_le_succ
  intro fuel
  have h := height_mono fuel (PlayerSpecificDivisionHeights.height_ge H)
  rw [height]
  omega

theorem loop_bounds (fuel : ℕ) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (loop fuel p q).gcd (height fuel H) ∧
      HasHeight (loop fuel p q).left (height fuel H) ∧
      HasHeight (loop fuel p q).right (height fuel H) ∧
      (loop fuel p q).gcd.length≤4 ∧
      (loop fuel p q).left.length≤1+4*fuel ∧ (loop fuel p q).right.length≤1+4*fuel := by
  induction fuel generalizing p q H with
  | zero =>
    exact ⟨mono (trim_height hp) (height_ge _ _),cons_height (one_height.mono (by simp only [height]; omega)) (nil_height _),
      nil_height _,(trim_length p).trans hpl,by simp only [loop,List.length_cons,List.length_nil]; omega,
      by simp only [loop,List.length_nil]; omega⟩
  | succ fuel ih =>
    rw [loop]
    split
    · exact ⟨mono (trim_height hp) (height_ge _ _),cons_height (one_height.mono (by have h:=height_ge (fuel+1) H; omega)) (nil_height _),
        nil_height _,(trim_length p).trans hpl,by simp only [List.length_cons,List.length_nil]; omega,
        by simp only [List.length_nil]; omega⟩
    · have hd := PlayerSpecificDivisionHeights.run_height p q H hp hq hH hpl hql
      have hD := PlayerSpecificDivisionHeights.height_ge H
      have hrlen := (PlayerSpecificDivisionHeights.remainder_length p q).trans hpl
      have hquotlen := (PlayerSpecificDivisionHeights.quotient_length p q).trans hpl
      have ht := ih q (PlayerSpecificPolynomialDivision.run p q).2 (PlayerSpecificDivisionHeights.height H)
        (mono hq hD) hd.2 (hH.trans hD) hql hrlen
      have hleft := ht.2.1
      have hright := ht.2.2.1
      have hglen := ht.2.2.2.1
      have hllen := ht.2.2.2.2.1
      have hrlen' := ht.2.2.2.2.2
      have hm := multiply_height hd.1 hright
      have hb := trim_height (subtract_height hleft hm)
      have hmul := Nat.mul_le_mul_left
        (PlayerSpecificDivisionHeights.height H+height fuel (PlayerSpecificDivisionHeights.height H)+1)
        (Nat.add_le_add_right hquotlen 1)
      have hsize := trim_length (subtract (loop fuel q (PlayerSpecificPolynomialDivision.run p q).2).left
        (multiply (PlayerSpecificPolynomialDivision.run p q).1 (loop fuel q (PlayerSpecificPolynomialDivision.run p q).2).right))
      rw [subtract,add_length,scale_length] at hsize
      have hprodsize := multiply_length (PlayerSpecificPolynomialDivision.run p q).1
        (loop fuel q (PlayerSpecificPolynomialDivision.run p q).2).right
      refine ⟨mono ht.1 ?_,mono hright ?_,mono hb ?_,hglen,?_,?_⟩
      · rw [height]; omega
      · rw [height]; omega
      · rw [height]; omega
      · exact hrlen'.trans (by omega)
      · have hh : max (loop fuel q (PlayerSpecificPolynomialDivision.run p q).2).left.length
            (multiply (PlayerSpecificPolynomialDivision.run p q).1 (loop fuel q (PlayerSpecificPolynomialDivision.run p q).2).right).length≤1+4*(fuel+1) := by
          apply max_le <;> omega
        exact hsize.trans hh

theorem run_bounds (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (run p q).gcd (height 4 H) ∧ HasHeight (run p q).left (height 4 H) ∧
      HasHeight (run p q).right (height 4 H) ∧ (run p q).gcd.length≤4 ∧
      (run p q).left.length≤17 ∧ (run p q).right.length≤17 := by
  have h := loop_bounds (trim q).length p (trim q) H hp (trim_height hq) hH hpl ((trim_length q).trans hql)
  have hl := (trim_length q).trans hql
  have hm := fuel_mono H hl
  exact ⟨mono h.1 hm,mono h.2.1 hm,mono h.2.2.1 hm,h.2.2.2.1,by dsimp only [run]; omega,by dsimp only [run]; omega⟩

def linearConstant : ℕ := (affine 4).1+(affine 4).2+1

theorem fixed_degree_linear (H : ℕ) : height 4 H≤linearConstant*(H+1) := by
  rw [height_affine]
  unfold linearConstant
  nlinarith

end Blotto.PlayerSpecificExtendedGCDHeights
