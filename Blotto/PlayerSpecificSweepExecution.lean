import Blotto.PlayerSpecificRecognitionScanContract

/-! Literal traced rational sweep arithmetic. Initial sums are accumulated
once; each moved field uses only fresh squared/quotiented input terms and
the five cached state scalars. Full field/state copies are included. -/
namespace Blotto.PlayerSpecificSweepExecution
open PlayerSpecificDensePolynomial PlayerSpecificSweep PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def copyState (s : State ℚ) : Trace :=
  copyRow [s.coefficients.A1,s.coefficients.A2,s.coefficients.B1,s.coefficients.B2,s.prefixMax]
def copyFields (fields : List (ℚ×ℚ)) : Trace :=
  [.control fields.length]++fields.flatMap (fun x => copyRow [x.1,x.2])

def initial : List (ℚ×ℚ) → State ℚ×Trace
  | [] =>
    let result:State ℚ:=⟨⟨0,0,0,0⟩,0⟩
    (result,copyState result++[.control 0])
  | x::xs =>
    let tail:=initial xs
    let square:=scalar .multiply x.2 x.2
    let term:=scalar .divide square.1 x.1
    let first:=scalar .add x.2 tail.1.coefficients.A1
    let third:=scalar .add term.1 tail.1.coefficients.B1
    let result:State ℚ:=⟨⟨first.1,0,third.1,0⟩,0⟩
    (result,tail.2++square.2++term.2++first.2++third.2++copyFields (x::xs)++copyState result++[.control (x::xs).length])

def move (s : State ℚ) (v w : ℚ) : State ℚ×Trace :=
  let squareV:=scalar .multiply v v
  let termV:=scalar .divide squareV.1 w
  let squareW:=scalar .multiply w w
  let termW:=scalar .divide squareW.1 v
  let first:=scalar .subtract s.coefficients.A1 w
  let second:=scalar .add s.coefficients.A2 termV.1
  let third:=scalar .subtract s.coefficients.B1 termW.1
  let fourth:=scalar .add s.coefficients.B2 v
  let compared:=PlayerSpecificRationalTrace.compare s.prefixMax v
  let prefixMax:=if compared.1 then v else s.prefixMax
  let result:State ℚ:=⟨⟨first.1,second.1,third.1,fourth.1⟩,prefixMax⟩
  (result,copyState s++copyRow [v,w]++squareV.2++termV.2++squareW.2++termW.2++
    first.2++second.2++third.2++fourth.2++compared.2++copyState result++[.control (if compared.1 then 1 else 0)])

theorem initial_value (fields : List (ℚ×ℚ)) : (initial fields).1=PlayerSpecificSweep.initial fields := by
  induction fields with
  | nil => rfl
  | cons x xs ih =>
    simp only [initial,ih,scalar,Arithmetic.apply,PlayerSpecificSweep.initial,List.map_cons,List.sum_cons,pow_two]

theorem move_value (s : State ℚ) (v w : ℚ) : (move s v w).1=PlayerSpecificSweep.move s v w := by
  by_cases h : s.prefixMax≤v
  · simp only [move,scalar,Arithmetic.apply,PlayerSpecificRationalTrace.compare,h,decide_true,ite_true,
      PlayerSpecificSweep.move,pow_two,max_eq_right h]
  · have hh : v≤s.prefixMax := (lt_of_not_ge h).le
    simp only [move,scalar,Arithmetic.apply,PlayerSpecificRationalTrace.compare,h,decide_false,Bool.false_eq_true,ite_false,
      PlayerSpecificSweep.move,pow_two,max_eq_left hh]

theorem copy_state_length (s : State ℚ) : (copyState s).length=6 := rfl
theorem copy_fields_length (fields : List (ℚ×ℚ)) : (copyFields fields).length=3*fields.length+1 := by
  simp only [copyFields,List.length_append,List.length_cons,List.length_nil,List.length_flatMap]
  induction fields with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,copyRow_length,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem initial_length (fields : List (ℚ×ℚ)) : (initial fields).2.length≤100*(fields.length+1)^2 := by
  induction fields with
  | nil => decide
  | cons x xs ih =>
    simp only [initial,List.length_append,scalar_length,copy_fields_length,copy_state_length,
      List.length_cons,List.length_nil] at ih ⊢
    nlinarith only [ih]

theorem move_length (s : State ℚ) (v w : ℚ) : (move s v w).2.length=60 := by
  simp only [move,List.length_append,copy_state_length,copyRow_length,scalar_length,compare_length,
    List.length_cons,List.length_nil]

end Blotto.PlayerSpecificSweepExecution
