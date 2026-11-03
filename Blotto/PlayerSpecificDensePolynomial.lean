import Blotto.PlayerSpecificRationalRecognition
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Executable dense rational polynomials for the finite-bit backend.
Coefficients are stored in ascending degree order. Only the proof-level
interpretation uses Mathlib's noncomputable Polynomial representation.
No root or sign oracle occurs in these numerical operations. -/
namespace Blotto.PlayerSpecificDensePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev Data := List ℚ

def evaluate (p : Data) (x : ℚ) : ℚ := p.foldr (fun a rest => a+x*rest) 0

def add : Data → Data → Data
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::add p q

def scale (a : ℚ) (p : Data) : Data := p.map (fun b => a*b)
def shift (p : Data) : Data := 0::p
def subtract (p q : Data) : Data := add p (scale (-1) q)

def multiply : Data → Data → Data
  | [],_ => []
  | a::p,q => add (scale a q) (shift (multiply p q))

def derivative : Data → Data
  | [] => []
  | _::p => add p (shift (derivative p))

def trim : Data → Data
  | [] => []
  | a::p =>
    let tail := trim p
    if tail=[] ∧ a=0 then [] else a::tail

noncomputable def semantics : Data → Polynomial ℚ
  | [] => 0
  | a::p => Polynomial.C a+Polynomial.X*semantics p

theorem evaluate_semantics (p : Data) (x : ℚ) : (semantics p).eval x=evaluate p x := by
  induction p with
  | nil => simp only [semantics,Polynomial.eval_zero,evaluate,List.foldr_nil]
  | cons a p ih => simp only [semantics,Polynomial.eval_add,Polynomial.eval_C,
      Polynomial.eval_mul,Polynomial.eval_X,ih,evaluate,List.foldr_cons]

theorem add_semantics (p q : Data) : semantics (add p q)=semantics p+semantics q := by
  induction p generalizing q with
  | nil => simp only [add,semantics,zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp only [add,semantics,add_zero]
    | cons b q => simp only [add,semantics,ih,Polynomial.C_add]; ring

theorem scale_semantics (a : ℚ) (p : Data) : semantics (scale a p)=Polynomial.C a*semantics p := by
  induction p with
  | nil => simp only [scale,List.map_nil,semantics,mul_zero]
  | cons b p ih =>
    dsimp only [scale] at ih
    simp only [scale,List.map_cons,semantics,Polynomial.C_mul,ih]
    ring

theorem shift_semantics (p : Data) : semantics (shift p)=Polynomial.X*semantics p := by
  simp only [shift,semantics,map_zero,zero_add]

theorem subtract_semantics (p q : Data) : semantics (subtract p q)=semantics p-semantics q := by
  rw [subtract,add_semantics,scale_semantics]
  simp only [map_neg,map_one,neg_one_mul,sub_eq_add_neg]

theorem multiply_semantics (p q : Data) : semantics (multiply p q)=semantics p*semantics q := by
  induction p with
  | nil => simp only [multiply,semantics,zero_mul]
  | cons a p ih => rw [multiply,add_semantics,scale_semantics,shift_semantics,ih,semantics]; ring

theorem derivative_semantics (p : Data) : semantics (derivative p)=Polynomial.derivative (semantics p) := by
  induction p with
  | nil => simp only [derivative,semantics,map_zero]
  | cons a p ih =>
    rw [derivative,add_semantics,shift_semantics,ih,semantics]
    simp only [Polynomial.derivative_add,Polynomial.derivative_C,Polynomial.derivative_mul,
      Polynomial.derivative_X,one_mul,zero_add]

theorem trim_semantics (p : Data) : semantics (trim p)=semantics p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [trim]
    split
    · rename_i h
      have ht : semantics p=0 := by rw [← ih,h.1]; rfl
      simp only [semantics,h.2,map_zero,ht,mul_zero,add_zero]
    · simp only [semantics,ih]

theorem trim_length (p : Data) : (trim p).length≤p.length := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih => rw [trim]; split <;> simp only [List.length_cons,List.length_nil] <;> omega

theorem add_length (p q : Data) : (add p q).length=max p.length q.length := by
  induction p generalizing q with
  | nil => simp only [add,List.length_nil,Nat.zero_max]
  | cons a p ih =>
    cases q with
    | nil => simp only [add,List.length_nil,Nat.max_zero]
    | cons b q => simp only [add,List.length_cons,ih]; omega

theorem scale_length (a : ℚ) (p : Data) : (scale a p).length=p.length := List.length_map _

theorem multiply_length (p q : Data) : (multiply p q).length≤p.length+q.length := by
  induction p with
  | nil => simp only [multiply,List.length_nil,Nat.zero_add]; omega
  | cons a p ih =>
    rw [multiply,add_length,scale_length]
    change max q.length ((multiply p q).length+1)≤_
    rw [max_le_iff]
    constructor <;> simp only [List.length_cons] <;> omega

theorem derivative_length (p : Data) : (derivative p).length≤p.length := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih => rw [derivative,add_length]; change max p.length ((derivative p).length+1)≤p.length+1; omega

def cubic (c : PlayerSpecificCubic.Coefficients ℚ) (b : ℚ) : Data :=
  [-b*c.A2,c.B2,-b*c.A1,c.B1]

theorem cubic_evaluate (c : PlayerSpecificCubic.Coefficients ℚ) (b x : ℚ) :
    evaluate (cubic c b) x=PlayerSpecificCubic.cubic c b x := by
  simp only [cubic,evaluate,List.foldr_cons,List.foldr_nil,PlayerSpecificCubic.cubic]
  ring

theorem cubic_semantics (c : PlayerSpecificCubic.Coefficients ℚ) (b : ℚ) :
    semantics (cubic c b)=PlayerSpecificPolynomial.polynomial c b := by
  simp only [cubic,semantics,PlayerSpecificPolynomial.polynomial,map_neg,map_mul,mul_zero,add_zero]
  ring

end Blotto.PlayerSpecificDensePolynomial
