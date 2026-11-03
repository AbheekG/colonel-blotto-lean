import Blotto.GeneralPaperBasisCoefficientScatter

/-! Materialize an ORIGINAL sparse affine row in the explicit coordinate
order by zero initialization and one additive scatter. Coefficients and
real evaluation agree exactly with the original sparse constraint.
-/
namespace Blotto.GeneralPaperBasisDenseRow
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperBasisCoordinates GeneralPaperBasisStoredProducts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Dense (d : ℕ) where
  coefficients : Vector d
  constant : ℤ
  slope : ℤ
  work : ℕ

def build {m K : ℕ} (r : Row (Variable m K)) : Dense (m*(K-1)) :=
  let terms := r.terms.map (fun term => (index term.1,term.2))
  let result := GeneralPaperBasisCoefficientScatter.run terms
  ⟨result.vector,r.constant,r.slope,result.work+8*r.terms.length+8⟩

theorem mapped_coefficient {m K : ℕ} (terms : List (Variable m K × ℤ)) (v : Variable m K) :
    coefficientTerms (terms.map (fun term => (index term.1,term.2))) (index v)=coefficientTerms terms v := by
  simp only [coefficientTerms,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  by_cases he : term.1=v
  · simp only [he,ite_true]
  · have hn : index term.1≠index v := fun h => he (index_injective m K h)
    simp only [he,hn,ite_false]

theorem build_read {m K : ℕ} (r : Row (Variable m K)) (v : Variable m K) :
    (build r).coefficients.read (index v)=r.coefficient v := by
  rw [build,GeneralPaperBasisCoefficientScatter.run_read,mapped_coefficient]
  rfl

theorem build_constant {m K : ℕ} (r : Row (Variable m K)) : (build r).constant=r.constant := rfl
theorem build_slope {m K : ℕ} (r : Row (Variable m K)) : (build r).slope=r.slope := rfl

theorem build_evaluate {m K : ℕ} (r : Row (Variable m K)) (x : Fin (m*(K-1)) → ℝ) :
    (∑ i,((build r).coefficients.read i:ℝ)*x i)=r.linear.evaluate (fun v => x (index v)) := by
  rw [←sum_index (fun i => ((build r).coefficients.read i:ℝ)*x i)]
  simp only [build_read]
  rw [LinearRow.evaluate_coefficients]
  rfl

theorem build_work {m K : ℕ} (r : Row (Variable m K)) :
    (build r).work≤64*(m*(K-1)+1)+24*r.terms.length+14 := by
  have hh := GeneralPaperBasisCoefficientScatter.run_work (r.terms.map (fun term => (index term.1,term.2)))
  simp only [List.length_map] at hh
  change (GeneralPaperBasisCoefficientScatter.run (r.terms.map (fun term => (index term.1,term.2)))).work+8*r.terms.length+8≤_
  omega

end Blotto.GeneralPaperBasisDenseRow
