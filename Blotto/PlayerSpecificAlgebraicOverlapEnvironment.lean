import Blotto.PlayerSpecificAlgebraicFourGluingInputs
import Blotto.RealOverlapDescriptorCompiler
import Blotto.OverlapFormulaBounds

/-! Native sixteen-row environments for overlap formulas reuse the
reached parent endpoints, weights, common interval and fallback budget. -/
namespace Blotto.PlayerSpecificAlgebraicOverlapEnvironment
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

def environment {k h : ℕ} (first : Descriptor 3 k) (second : Descriptor 3 h) (interval budget : Data)
    (i : Fin k) (j : Fin h) : FixedArrayTable 16 Data :=
  FixedArrayTable.ofFn ![(first.first.read i).read 0,(first.first.read i).read 1,(first.first.read i).read 2,
    (first.second.read i).read 0,(first.second.read i).read 1,(first.second.read i).read 2,
    (second.first.read j).read 0,(second.first.read j).read 1,(second.first.read j).read 2,
    (second.second.read j).read 0,(second.second.read j).read 1,(second.second.read j).read 2,
    first.weights.read i,second.weights.read j,interval,budget]

theorem value {k h : ℕ} (first : Descriptor 3 k) (second : Descriptor 3 h) (interval budget : Data)
    (x : ℝ) (G : OverlapGluing k h) (B : ℝ) (hf : Refines first x G.first) (hs : Refines second x G.second)
    (hi : realEvaluate interval x=G.d) (hb : realEvaluate budget x=B) (i : Fin k) (j : Fin h) :
    PlayerSpecificAlgebraicExpression.realEnv (environment first second interval budget i j) x=RealOverlapFormula.environment G B i j := by
  unfold PlayerSpecificAlgebraicExpression.realEnv RealOverlapFormula.environment
  congr 1
  funext r
  have hp := congrFun (hf.first i)
  have hq := congrFun (hf.second i)
  have hsP := congrFun (hs.first j)
  have hsQ := congrFun (hs.second j)
  fin_cases r <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact hp 0
  · exact hp 1
  · exact hp 2
  · exact hq 0
  · exact hq 1
  · exact hq 2
  · exact hsP 0
  · exact hsP 1
  · exact hsP 2
  · exact hsQ 0
  · exact hsQ 1
  · exact hsQ 2
  · exact hf.weights i
  · exact hs.weights j
  · exact hi
  · exact hb

theorem bounds {k h : ℕ} (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h) (interval budget : Data)
    (T : ℕ) (hf : Bounds root first T) (hs : Bounds root second T)
    (hi : Reduced root.polynomial interval ∧ HasHeight interval T) (hb : Reduced root.polynomial budget ∧ HasHeight budget T)
    (i : Fin k) (j : Fin h) : ∀ r,Reduced root.polynomial ((environment first second interval budget i j).read r) ∧
      HasHeight ((environment first second interval budget i j).read r) T := by
  intro r
  fin_cases r <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact hf.first i 0
  · exact hf.first i 1
  · exact hf.first i 2
  · exact hf.second i 0
  · exact hf.second i 1
  · exact hf.second i 2
  · exact hs.first j 0
  · exact hs.first j 1
  · exact hs.first j 2
  · exact hs.second j 0
  · exact hs.second j 1
  · exact hs.second j 2
  · exact hf.weights i
  · exact hs.weights j
  · exact hi
  · exact hb

end Blotto.PlayerSpecificAlgebraicOverlapEnvironment
