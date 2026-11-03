import Blotto.PlayerSpecificRootIsolation

/-! Bounds for the actual stored rational coefficients and Horner arithmetic.
These bounds follow the implemented dense operations, including padding,
zero coefficients, cancellation and leading-zero removal. -/
namespace Blotto.PlayerSpecificPolynomialHeights
open PlayerSpecificDensePolynomial PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 4000000

def HasHeight (p : Data) (s : ℕ) : Prop := ∀ q∈p,RationalHeight q s

theorem zero_height : RationalHeight (0:ℚ) 1 := by norm_num [RationalHeight]
theorem one_height : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]

theorem nil_height (s : ℕ) : HasHeight [] s := by intro q h; cases h

theorem mono {p : Data} {s t : ℕ} (h : HasHeight p s) (hst : s≤t) : HasHeight p t :=
  fun q hq => (h q hq).mono hst

theorem cons_height {p : Data} {a : ℚ} {s : ℕ} (ha : RationalHeight a s) (hp : HasHeight p s) :
    HasHeight (a::p) s := by
  intro q hq
  rcases List.mem_cons.mp hq with he | ht
  · subst q; exact ha
  · exact hp q ht

theorem tail_height {p : Data} {a : ℚ} {s : ℕ} (h : HasHeight (a::p) s) : HasHeight p s :=
  fun q hq => h q (List.mem_cons_of_mem a hq)

theorem head_height {p : Data} {a : ℚ} {s : ℕ} (h : HasHeight (a::p) s) : RationalHeight a s :=
  h a List.mem_cons_self

theorem input_height (p : Data) : HasHeight p (inputHeight p) := member_height p

theorem trim_height {p : Data} {s : ℕ} (h : HasHeight p s) : HasHeight (trim p) s :=
  fun q hq => h q (trim_member p q hq)

theorem default_height {p : Data} {s : ℕ} (h : HasHeight p s) (hs : 1≤s) :
    RationalHeight (p.getLast?.getD 0) s := by
  cases he : p.getLast? with
  | none => simpa only [he,Option.getD_none] using zero_height.mono hs
  | some q => simpa only [he,Option.getD_some] using h q (List.mem_of_getLast? he)

theorem add_height {p q : Data} {s t : ℕ} (hp : HasHeight p s) (hq : HasHeight q t) :
    HasHeight (add p q) (s+t+1) := by
  induction p generalizing q with
  | nil => exact mono hq (by omega)
  | cons a p ih =>
    cases q with
    | nil => exact mono hp (by omega)
    | cons b q =>
      exact cons_height ((head_height hp).add (head_height hq)) (ih (tail_height hp) (tail_height hq))

theorem scale_height {p : Data} {a : ℚ} {s t : ℕ} (ha : RationalHeight a s) (hp : HasHeight p t) :
    HasHeight (scale a p) (s+t) := by
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  exact ha.mul (hp r hr)

theorem negative_height {p : Data} {s : ℕ} (hp : HasHeight p s) : HasHeight (scale (-1) p) s := by
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  simpa only [neg_one_mul] using (hp r hr).neg

theorem subtract_height {p q : Data} {s t : ℕ} (hp : HasHeight p s) (hq : HasHeight q t) :
    HasHeight (subtract p q) (s+t+1) := add_height hp (negative_height hq)

theorem shift_height {p : Data} {s : ℕ} (hp : HasHeight p s) (hs : 1≤s) : HasHeight (shift p) s :=
  cons_height (zero_height.mono hs) hp

theorem multiply_height {p q : Data} {s t : ℕ} (hp : HasHeight p s) (hq : HasHeight q t) :
    HasHeight (multiply p q) ((s+t+1)*(p.length+1)) := by
  induction p with
  | nil => exact nil_height _
  | cons a p ih =>
    have ht := ih (tail_height hp)
    have hz : 1≤(s+t+1)*(p.length+1) := Nat.mul_pos (by omega) (by omega)
    have hh := add_height (scale_height (head_height hp) hq) (shift_height ht hz)
    apply mono hh
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem derivative_height {p : Data} {s : ℕ} (hp : HasHeight p s) :
    HasHeight (derivative p) ((s+1)*(p.length+1)) := by
  induction p with
  | nil => exact nil_height _
  | cons a p ih =>
    have ht := ih (tail_height hp)
    have hz : 1≤(s+1)*(p.length+1) := Nat.mul_pos (by omega) (by omega)
    have hh := add_height (tail_height hp) (shift_height ht hz)
    apply mono hh
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem evaluate_height {p : Data} {x : ℚ} {s t : ℕ} (hp : HasHeight p s) (hx : RationalHeight x t) :
    RationalHeight (evaluate p x) ((s+t+1)*p.length+1) := by
  induction p with
  | nil => exact zero_height
  | cons a p ih =>
    have hh := (head_height hp).add (hx.mul (ih (tail_height hp)))
    apply hh.mono
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem total_width {p : Data} {s : ℕ} (hp : HasHeight p s) :
    RationalAggregateRecognitionCost.totalWidth p≤p.length*(1+2*s) := by
  induction p with
  | nil => simp only [RationalAggregateRecognitionCost.totalWidth,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons a p ih =>
    have ha := rationalWordWidth_of_height (head_height hp)
    have ht := ih (tail_height hp)
    dsimp only [RationalAggregateRecognitionCost.totalWidth] at ht ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

theorem inputHeight_le {p : Data} {s : ℕ} (hp : HasHeight p s) :
    inputHeight p≤p.length*(1+2*s)+1 := Nat.add_le_add_right (total_width hp) 1

end Blotto.PlayerSpecificPolynomialHeights
