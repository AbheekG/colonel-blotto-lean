import Blotto.PlayerSpecificAlgebraicComplementaryDraw

/-! Three-coordinate terminal draws share a four-row group interface.
Uniform triples append zero; a two-group mixed triple places its mixture
last and leaves the third uniform slot zero. No arithmetic is performed. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalEmbedding
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

def uniform (y : FixedArrayTable 3 Data) : FixedArrayTable 4 Data :=
  FixedArrayTable.ofFn ![y.read 0,y.read 1,y.read 2,[]]

def mixed (y : FixedArrayTable 3 Data) : FixedArrayTable 4 Data :=
  FixedArrayTable.ofFn ![y.read 0,y.read 1,[],y.read 2]

theorem uniform_value (y : FixedArrayTable 3 Data) (x : ℝ) :
    values (uniform y) x=![values y x 0,values y x 1,values y x 2,0] := by
  have hz : realEvaluate [] x=0 := rfl
  funext j
  fin_cases j <;> simp [uniform,values,FixedArrayTable.read_ofFn,hz]

theorem mixed_value (y : FixedArrayTable 3 Data) (x : ℝ) :
    values (mixed y) x=![values y x 0,values y x 1,0,values y x 2] := by
  have hz : realEvaluate [] x=0 := rfl
  funext j
  fin_cases j <;> simp [mixed,values,FixedArrayTable.read_ofFn,hz]

theorem uniform_budget (y : FixedArrayTable 3 Data) (x B : ℝ) (hy : FullBudget B (values y x)) :
    FullBudget B (values (uniform y) x) := by
  rw [uniform_value]
  constructor
  · intro j
    fin_cases j
    · exact hy.1 0
    · exact hy.1 1
    · exact hy.1 2
    · exact le_rfl
  · simpa [Fin.sum_univ_succ] using hy.2

theorem mixed_budget (y : FixedArrayTable 3 Data) (x B : ℝ) (hy : FullBudget B (values y x)) :
    FullBudget B (values (mixed y) x) := by
  rw [mixed_value]
  constructor
  · intro j
    fin_cases j
    · exact hy.1 0
    · exact hy.1 1
    · exact le_rfl
    · exact hy.1 2
  · simpa [Fin.sum_univ_succ] using hy.2

theorem uniform_bounds (root : Candidate) (y : FixedArrayTable 3 Data) (T : ℕ) (hm0 : root.polynomial ≠ [])
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    ∀ j,Reduced root.polynomial ((uniform y).read j) ∧ HasHeight ((uniform y).read j) T := by
  intro j
  fin_cases j <;> simp only [uniform,FixedArrayTable.read_ofFn]
  · exact hy 0
  · exact hy 1
  · exact hy 2
  · exact ⟨nil_reduced _ hm0,nil_height _⟩

theorem mixed_bounds (root : Candidate) (y : FixedArrayTable 3 Data) (T : ℕ) (hm0 : root.polynomial ≠ [])
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    ∀ j,Reduced root.polynomial ((mixed y).read j) ∧ HasHeight ((mixed y).read j) T := by
  intro j
  fin_cases j <;> simp only [mixed,FixedArrayTable.read_ofFn]
  · exact hy 0
  · exact hy 1
  · exact ⟨nil_reduced _ hm0,nil_height _⟩
  · exact hy 2

end Blotto.PlayerSpecificAlgebraicTerminalEmbedding
