import Blotto.PlayerSpecificAlgebraicTerminalLeafExecution

/-! Every emitted leaf uses two fixed field-arithmetic layers from its
original length, cached group total and sampled group value. The number
of original leaves introduces no multiplicative chain of coefficients. -/
namespace Blotto.PlayerSpecificAlgebraicLeafHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicGrouping
open PlayerSpecificAlgebraicLeafAssignments PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem patch_bounds {N : ℕ} (root : Candidate) (a : FixedArrayTable N Data) (es : List (Fin N × Data)) (T : ℕ)
    (ha : ∀ j,Reduced root.polynomial (a.read j) ∧ HasHeight (a.read j) T)
    (he : ∀ e ∈ es,Reduced root.polynomial e.2 ∧ HasHeight e.2 T) :
    ∀ j,Reduced root.polynomial ((a.patch es).read j) ∧ HasHeight ((a.patch es).read j) T := by
  induction es generalizing a with
  | nil => exact ha
  | cons e es ih =>
    rw [FixedArrayTable.patch]
    apply ih
    · intro j
      rw [FixedArrayTable.read_write]
      by_cases hj : j=e.1
      · rw [ite_eq_left hj]
        exact he e (by simp)
      · rw [ite_eq_right hj]
        exact ha j
    · intro e he0
      exact he e (by simp [he0])

theorem assignment_bounds {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T)
    (hL : ∀ j,Reduced root.polynomial (length j) ∧ HasHeight (length j) T)
    (hG : ∀ g ∈ groups,Reduced root.polynomial g.total ∧ HasHeight g.total T)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    ∀ e ∈ assignments root length groups y,Reduced root.polynomial e.2 ∧ HasHeight e.2 (iterate 2 T) := by
  have hle : T ≤ step T := (Nat.le_succ _).trans (large T)
  intro e he
  obtain ⟨g,_,hv⟩ := (mem_assignments root length groups y e).mp he
  rw [hv]
  have hg := hG _ (List.get_mem groups g)
  have hq := divide_height root.polynomial (length e.1) (groups.get g).total T hm hm0 hml
    (hL e.1).1 hg.1 hmT (hL e.1).2 hg.2 hT
  exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
    times_height _ _ _ (step T) hm hm0 hml (PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0)
      (hy (slot g)).1 (PlayerSpecificPolynomialHeights.mono hmT hle) hq
      (PlayerSpecificPolynomialHeights.mono (hy (slot g)).2 hle)⟩

theorem emit_bounds {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T)
    (hL : ∀ j,Reduced root.polynomial (length j) ∧ HasHeight (length j) T)
    (hG : ∀ g ∈ groups,Reduced root.polynomial g.total ∧ HasHeight g.total T)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    ∀ j,Reduced root.polynomial ((emit root length groups y).read j) ∧
      HasHeight ((emit root length groups y).read j) (iterate 2 T) := by
  apply patch_bounds
  · intro j
    rw [FixedArrayTable.read_ofFn]
    exact ⟨nil_reduced _ hm0,nil_height _⟩
  · exact assignment_bounds root length groups y T hm hm0 hml hmT hT hL hG hy

theorem mixed_bounds {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (fractional : Option (Fin N)) (y : FixedArrayTable 4 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T)
    (hL : ∀ j,Reduced root.polynomial (length j) ∧ HasHeight (length j) T)
    (hG : ∀ g ∈ groups,Reduced root.polynomial g.total ∧ HasHeight g.total T)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    ∀ j,Reduced root.polynomial ((emitMixed root length groups fractional y).read j) ∧
      HasHeight ((emitMixed root length groups fractional y).read j) (iterate 2 T) := by
  have he := emit_bounds root length groups y T hm hm0 hml hmT hT hL hG hy
  cases fractional with
  | none => exact he
  | some k =>
    intro j
    rw [emitMixed,FixedArrayTable.read_write]
    by_cases hj : j=k
    · rw [ite_eq_left hj]
      exact ⟨(hy 3).1,PlayerSpecificPolynomialHeights.mono (hy 3).2 (PlayerSpecificAlgebraicExpressionBudget.initial_le 2 T)⟩
    · rw [ite_eq_right hj]
      exact he j

theorem height_linear (T : ℕ) : iterate 2 T+1 ≤ (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^2*(T+1) :=
  iterate_bound 2 T

end Blotto.PlayerSpecificAlgebraicLeafHeights
