import Blotto.PlayerSpecificRationalTrace

/-! Executed dense-polynomial operations paired with operand-sized source
traces. Each numerical return refines the previously verified operation.
The trace conservatively includes complete returned-list copies, in addition
to scalar operand/result copies and explicit control words. -/
namespace Blotto.PlayerSpecificDenseExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def finish (row : Data) (trace : Trace) : Data×Trace := (row,trace++copyRow row)

def add : Data → Data → Data×Trace
  | [],q => finish q [.control 0,.control q.length]
  | p,[] => finish p [.control p.length,.control 0]
  | a::p,b::q =>
    let head := scalar .add a b
    let tail := add p q
    finish (head.1::tail.1) ([.control (p.length+1),.control (q.length+1)]++head.2++tail.2)

def scale (a : ℚ) : Data → Data×Trace
  | [] => finish [] [.copy a,.control 0]
  | b::p =>
    let head := scalar .multiply a b
    let tail := scale a p
    finish (head.1::tail.1) ([.control (p.length+1)]++head.2++tail.2)

def shift (p : Data) : Data×Trace := finish (0::p) (copyRow p++[.control p.length,.copy 0])

def subtract (p q : Data) : Data×Trace :=
  let negated := scale (-1) q
  let added := add p negated.1
  finish added.1 (negated.2++added.2)

def multiply : Data → Data → Data×Trace
  | [],q => finish [] (copyRow q++[.control 0])
  | a::p,q =>
    let scaled := scale a q
    let tail := multiply p q
    let shifted := shift tail.1
    let added := add scaled.1 shifted.1
    finish added.1 ([.control (p.length+1)]++scaled.2++tail.2++shifted.2++added.2)

def derivative : Data → Data×Trace
  | [] => finish [] [.control 0]
  | a::p =>
    let tail := derivative p
    let shifted := shift tail.1
    let added := add p shifted.1
    finish added.1 ([.copy a,.control (p.length+1)]++tail.2++shifted.2++added.2)

def trim : Data → Data×Trace
  | [] => finish [] [.control 0]
  | a::p =>
    let tail := trim p
    let zero := equalZero a
    let result := if tail.1=[] ∧ zero.1=true then [] else a::tail.1
    finish result (tail.2++zero.2++[.control tail.1.length,.control 1])

def evaluate : Data → ℚ → ℚ×Trace
  | [],x => (0,[.copy x,.copy 0,.control 0])
  | a::p,x =>
    let tail := evaluate p x
    let product := scalar .multiply x tail.1
    let sum := scalar .add a product.1
    (sum.1,[.control (p.length+1)]++tail.2++product.2++sum.2)

theorem finish_value (row : Data) (trace : Trace) : (finish row trace).1=row := rfl

theorem add_value (p q : Data) : (add p q).1=PlayerSpecificDensePolynomial.add p q := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q => simpa only [add,finish,scalar,Arithmetic.apply,PlayerSpecificDensePolynomial.add] using congrArg (List.cons (a+b)) (ih q)

theorem scale_value (a : ℚ) (p : Data) : (scale a p).1=PlayerSpecificDensePolynomial.scale a p := by
  induction p with
  | nil => rfl
  | cons b p ih => simpa only [scale,finish,scalar,Arithmetic.apply,PlayerSpecificDensePolynomial.scale,List.map_cons] using congrArg (List.cons (a*b)) ih

theorem shift_value (p : Data) : (shift p).1=PlayerSpecificDensePolynomial.shift p := rfl

theorem subtract_value (p q : Data) : (subtract p q).1=PlayerSpecificDensePolynomial.subtract p q := by
  simp only [subtract,finish,add_value,scale_value,PlayerSpecificDensePolynomial.subtract]

theorem multiply_value (p q : Data) : (multiply p q).1=PlayerSpecificDensePolynomial.multiply p q := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [multiply,finish,add_value,shift_value,scale_value,ih,PlayerSpecificDensePolynomial.multiply]

theorem derivative_value (p : Data) : (derivative p).1=PlayerSpecificDensePolynomial.derivative p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [derivative,finish,add_value,shift_value,ih,PlayerSpecificDensePolynomial.derivative]

theorem trim_value (p : Data) : (trim p).1=PlayerSpecificDensePolynomial.trim p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [trim,finish,equalZero,decide_eq_true_eq,ih,PlayerSpecificDensePolynomial.trim]

theorem evaluate_value (p : Data) (x : ℚ) : (evaluate p x).1=PlayerSpecificDensePolynomial.evaluate p x := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [evaluate,scalar,Arithmetic.apply,ih,PlayerSpecificDensePolynomial.evaluate,List.foldr_cons]

theorem evaluate_trace_length (p : Data) (x : ℚ) : (evaluate p x).2.length=11*p.length+3 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [evaluate,List.length_append,List.length_cons,List.length_nil,scalar_length,ih]
    omega

end Blotto.PlayerSpecificDenseExecution
