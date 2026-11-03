import Blotto.PlayerSpecificAlgebraicCandidateTest

/-! The separate rational-breakpoint test remains an actual exact rational
calculation. Its accepted root is retained as a degree-one representation. -/
namespace Blotto.PlayerSpecificRationalBreakpoint
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

def candidate (q : ℚ) : Candidate := ⟨PlayerSpecificLinearFactor.linear q,⟨q-1,q,0,0⟩⟩
abbrev passes (c : Cell) (b q : ℚ) : Prop :=
  max c.state.prefixMax (q*c.suffixMax)≤b*PlayerSpecificCubic.candidateScale c.state.coefficients b q
def run (c : Cell) (b : ℚ) : Option Candidate :=
  match c.upper with
  | none => none
  | some q => if 0<q ∧ c.lower≤q ∧ evaluate (cubic c.state.coefficients b) q=0 ∧ passes c b q
      then some (candidate q) else none

theorem passes_cast (c : Cell) (b q : ℚ) : passes c b q ↔ PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) (q:ℝ) := by
  dsimp only [passes,PlayerSpecificCellCandidates.Passes,PlayerSpecificCubic.candidateScale,castCell,castState,castCoefficients]
  constructor <;> intro h <;> exact_mod_cast h

theorem candidate_root (q : ℚ) :
    ∃! x : ℝ,realEvaluate (candidate q).polynomial x=0 ∧ (candidate q).interval.Contains x := by
  refine ⟨(q:ℝ),⟨?_,?_⟩,?_⟩
  · change realEvaluate (PlayerSpecificLinearFactor.linear q) (q:ℝ)=0
    rw [PlayerSpecificAlgebraicCandidates.linear_real,sub_self]
  · change (((q-1:ℚ):ℝ)<(q:ℝ)) ∧ (q:ℝ)≤(q:ℝ)
    constructor
    · push_cast; linarith
    · exact le_refl _
  · intro x hx
    exact sub_eq_zero.mp ((PlayerSpecificAlgebraicCandidates.linear_real q x).symm.trans hx.1)

theorem correct (c : Cell) (b : ℚ) (q : ℚ) :
    run c b=some (candidate q) ↔ (q:ℝ)∈PlayerSpecificCellCandidates.breakpoints (castCell c) (b:ℝ) ∧ passes c b q := by
  cases hu : c.upper with
  | none =>
    have huR : (castCell c).upper=none := by simp only [castCell,hu,Option.map_none]
    simp only [run,hu,PlayerSpecificCellCandidates.breakpoints,huR,List.not_mem_nil,false_and]
    simp
  | some r =>
    have huR : (castCell c).upper=some (r:ℝ) := by simp only [castCell,hu,Option.map_some]
    have hroot : evaluate (cubic c.state.coefficients b) r=0 ↔
        PlayerSpecificCubic.cubic (castCell c).state.coefficients (b:ℝ) (r:ℝ)=0 := by
      rw [←PlayerSpecificRationalIntervals.cubic_value,evaluate_cast,Rat.cast_eq_zero]
    have hbase : (0<r ∧ c.lower≤r ∧ evaluate (cubic c.state.coefficients b) r=0) ↔
        ((0:ℝ)<(r:ℝ) ∧ (c.lower:ℝ)≤(r:ℝ) ∧ PlayerSpecificCubic.cubic (castCell c).state.coefficients (b:ℝ) (r:ℝ)=0) := by
      rw [←hroot]
      norm_cast
    have hmem : (q:ℝ)∈PlayerSpecificCellCandidates.breakpoints (castCell c) (b:ℝ) ↔
        q=r ∧ (0<r ∧ c.lower≤r ∧ evaluate (cubic c.state.coefficients b) r=0) := by
      rw [PlayerSpecificCellCandidates.breakpoints,huR]
      change (q:ℝ)∈(if (0:ℝ)<(r:ℝ) ∧ (c.lower:ℝ)≤(r:ℝ) ∧
          PlayerSpecificCubic.cubic (castCell c).state.coefficients (b:ℝ) (r:ℝ)=0 then [(r:ℝ)] else []) ↔ _
      simp only [←hbase]
      by_cases ht : 0<r ∧ c.lower≤r ∧ evaluate (cubic c.state.coefficients b) r=0
      · simp only [ht,ite_true,List.mem_singleton,Rat.cast_inj,and_true]
      · simp only [ht,ite_false,List.not_mem_nil,and_false]
    rw [hmem]
    simp only [run,hu]
    by_cases ht : 0<r ∧ c.lower≤r ∧ evaluate (cubic c.state.coefficients b) r=0 ∧ passes c b r
    · rw [ite_eq_left ht,Option.some.injEq]
      constructor
      · intro he
        have heq : r=q := congrArg (fun z => z.interval.hi) he
        subst r
        exact ⟨⟨rfl,ht.1,ht.2.1,ht.2.2.1⟩,ht.2.2.2⟩
      · intro h
        have heq:=h.1.1
        exact congrArg candidate heq.symm
    · rw [ite_eq_right ht]
      constructor
      · intro h
        cases h
      · rintro ⟨⟨he,hpos,hlo,hroot⟩,hpass⟩
        subst q
        exact (ht ⟨hpos,hlo,hroot,hpass⟩).elim

end Blotto.PlayerSpecificRationalBreakpoint
