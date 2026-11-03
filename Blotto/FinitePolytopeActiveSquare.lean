import Blotto.FinitePolytopeActiveKernel
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The active-kernel property selects an actual nonsingular square active
subsystem. A basis is constructed INSIDE the span of the actual active row
vectors, then reindexed to the original finite coordinate type. No supplied
vertex, active basis or nonsingular matrix oracle is used by the order-cell
endpoint. Integer determinant magnitude/Cramer/common-denominator bounds are
assembled in FinitePolytopeRationalWitness. Imports reuse existing pinned local artifacts. -/

namespace Blotto.FinitePolytopeActiveSquare
open Set RationalOrderCell FinitePolytopeVertex FinitePolytopeActiveKernel
open scoped BigOperators Classical

abbrev Active {r d : Type*} (rows : r → LinearRow d) (vertex : d → ℝ) :=
  {row : r // (rows row).residual vertex = 0}

noncomputable def activeVector {r d : Type*} [DecidableEq d] (rows : r → LinearRow d)
    (vertex : d → ℝ) (row : Active rows vertex) : d → ℝ :=
  fun coordinate => ((rows row.1).coefficient coordinate : ℝ)

theorem active_columns_independent {r d : Type*} [Fintype r] [Fintype d] [DecidableEq d]
    (rows : r → LinearRow d) (vertex : d → ℝ) (hVertex : MidpointVertex (halfspaces rows) vertex) :
    LinearIndependent ℝ (fun coordinate => fun row : Active rows vertex => activeVector rows vertex row coordinate) := by
  apply Fintype.linearIndependent_iff.mpr
  intro weights hWeights coordinate
  have hKernel : ∀ row, (rows row).residual vertex = 0 → (rows row).evaluate weights = 0 := by
    intro row hActive
    have h := congrFun hWeights (⟨row,hActive⟩ : Active rows vertex)
    rw [(rows row).evaluate_coefficients]
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,activeVector,mul_comm] using h
  exact congrFun (active_kernel_trivial rows vertex hVertex weights hKernel) coordinate

theorem active_rows_span {r d : Type*} [Fintype r] [Fintype d] [DecidableEq d]
    (rows : r → LinearRow d) (vertex : d → ℝ) (hVertex : MidpointVertex (halfspaces rows) vertex) :
    Submodule.span ℝ (Set.range (activeVector rows vertex)) = ⊤ := by
  have h := span_flip_eq_top_iff_linearIndependent.mpr (active_columns_independent rows vertex hVertex)
  exact h

theorem exists_active_square {r d : Type*} [Fintype r] [Fintype d] [DecidableEq d]
    (rows : r → LinearRow d) (vertex : d → ℝ) (hVertex : MidpointVertex (halfspaces rows) vertex) :
    ∃ selected : d → Active rows vertex,
      Matrix.det (fun i j => activeVector rows vertex (selected i) j : Matrix d d ℝ) ≠ 0 := by
  have hSpan := active_rows_span rows vertex hVertex
  let basis := Module.Basis.ofSpan hSpan.ge
  let reindex := basis.indexEquiv (Pi.basisFun ℝ d)
  have hSelection : ∀ coordinate : d, ∃ row : Active rows vertex,
      activeVector rows vertex row = basis (reindex.symm coordinate) := by
    intro coordinate
    exact Module.Basis.ofSpan_subset hSpan.ge ⟨reindex.symm coordinate,rfl⟩
  choose selected hSelected using hSelection
  let matrix : Matrix d d ℝ := fun i j => activeVector rows vertex (selected i) j
  have hIndependent : LinearIndependent ℝ matrix.row := by
    have h := basis.linearIndependent.comp reindex.symm reindex.symm.injective
    convert h using 1
    funext coordinate
    exact hSelected coordinate
  have hUnit := Matrix.linearIndependent_rows_iff_isUnit.mp hIndependent
  exact ⟨selected,((Matrix.isUnit_iff_isUnit_det matrix).mp hUnit).ne_zero⟩

/-- The real vertex and selected square active system are BOTH derived from
the original real anchor data, including for a lower-dimensional cell. -/
theorem order_cell_has_active_square {m K : ℕ} (budgets : Fin 2 → ℚ)
    (original : Variable m K → ℝ) (hOriginal : ∀ v, original v ∈ Icc (0 : ℝ) 1) :
    ∃ vertex : Coordinate m K → ℝ, FeasibleCell budgets original vertex ∧ 0 < vertex none ∧
      ∃ selected : Coordinate m K → Active (constraint budgets original) vertex,
        Matrix.det (fun i j => activeVector (constraint budgets original) vertex (selected i) j :
          Matrix (Coordinate m K) (Coordinate m K) ℝ) ≠ 0 := by
  obtain ⟨vertex,hVertex,hPositive,_hMax⟩ := order_cell_has_positive_vertex budgets original hOriginal
  exact ⟨vertex,hVertex.1,hPositive,exists_active_square (constraint budgets original) vertex hVertex⟩

end Blotto.FinitePolytopeActiveSquare
