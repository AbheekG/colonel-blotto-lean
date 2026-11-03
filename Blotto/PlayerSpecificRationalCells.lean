import Blotto.PlayerSpecificSignContract

/-! Computable rational cells for the finite-bit recognition sweep. The
retained four sums and prefix/suffix maxima use exact rational arithmetic.
Casting reproduces the preserved real interval records exactly. -/
namespace Blotto.PlayerSpecificRationalCells
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificSweepBounds
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Cell where
  state : State ℚ
  lower : ℚ
  upper : Option ℚ
  suffixMax : ℚ

def build (s : State ℚ) (lower : ℚ) : List ((ℚ×ℚ)×ℚ) → List Cell
  | [] => [⟨s,lower,none,0⟩]
  | (x,m)::xs => ⟨s,lower,some (x.1/x.2),m⟩::build (move s x.1 x.2) (x.1/x.2) xs

noncomputable def castCoefficients (c : Coefficients ℚ) : Coefficients ℝ := ⟨c.A1,c.A2,c.B1,c.B2⟩
noncomputable def castState (s : State ℚ) : State ℝ := ⟨castCoefficients s.coefficients,s.prefixMax⟩
noncomputable def castPair (x : ℚ×ℚ) : ℝ×ℝ := (x.1,x.2)
noncomputable def castSuffix (x : (ℚ×ℚ)×ℚ) : (ℝ×ℝ)×ℝ := (castPair x.1,x.2)
noncomputable def castCell (c : Cell) : PlayerSpecificCells.Cell := ⟨castState c.state,c.lower,c.upper.map (fun (q:ℚ) => (q:ℝ)),c.suffixMax⟩

theorem count (s : State ℚ) (lower : ℚ) (xs : List ((ℚ×ℚ)×ℚ)) : (build s lower xs).length=xs.length+1 := by
  induction xs generalizing s lower with
  | nil => rfl
  | cons x xs ih => simp only [build,List.length_cons,ih]

theorem cast_sum (xs : List ℚ) : (xs.sum:ℝ)=(xs.map (fun (q:ℚ) => (q:ℝ))).sum := by
  induction xs with
  | nil => simp only [List.sum_nil,List.map_nil,Rat.cast_zero]
  | cons x xs ih => simp only [List.sum_cons,List.map_cons,Rat.cast_add,ih]

theorem initial_cast (fields : List (ℚ×ℚ)) : castState (initial fields)=initial (fields.map castPair) := by
  simp only [castState,castCoefficients,initial,cast_sum,Rat.cast_zero,List.map_map,Function.comp_def,
    castPair,Rat.cast_div,Rat.cast_pow]

theorem move_cast (s : State ℚ) (v w : ℚ) : castState (move s v w)=move (castState s) (v:ℝ) (w:ℝ) := by
  simp only [castState,castCoefficients,move,Rat.cast_sub,Rat.cast_add,Rat.cast_pow,Rat.cast_div,Rat.cast_max]

theorem suffixes_cast (fields : List (ℚ×ℚ)) :
    ((suffixes fields).1:ℝ)=(suffixes (fields.map castPair)).1 ∧
      ((suffixes fields).2.1.map castSuffix)=(suffixes (fields.map castPair)).2.1 := by
  induction fields with
  | nil => exact ⟨by simp only [suffixes,List.map_nil,Rat.cast_zero],rfl⟩
  | cons x xs ih =>
    simp only [suffixes,List.map_cons,castPair,castSuffix,Rat.cast_max,ih.1,ih.2,and_self]

theorem build_cast (s : State ℚ) (lower : ℚ) (xs : List ((ℚ×ℚ)×ℚ)) :
    (build s lower xs).map castCell=(PlayerSpecificCells.build (castState s) (lower:ℝ) (xs.map castSuffix)).1 := by
  induction xs generalizing s lower with
  | nil => simp only [build,PlayerSpecificCells.build,List.map_cons,List.map_nil,castCell,Option.map_none,Rat.cast_zero]
  | cons x xs ih =>
    simp only [build,PlayerSpecificCells.build,List.map_cons,castSuffix,castPair,castCell,Option.map_some,
      ih,move_cast,Rat.cast_div]

end Blotto.PlayerSpecificRationalCells
