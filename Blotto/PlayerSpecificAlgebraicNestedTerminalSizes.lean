import Blotto.PlayerSpecificAlgebraicNestedTerminalInput

/-! A reached nested terminal input copies endpoint rows and performs
one mixture division, adding just one coefficient-height layer. -/
namespace Blotto.PlayerSpecificAlgebraicNestedTerminalSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedTerminalInput
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

structure Fits (root : Candidate) (a : Input) (T : ℕ) : Prop where
  budget : Reduced root.polynomial a.budget ∧ HasHeight a.budget T
  long : ∀ j,Reduced root.polynomial (a.long.read j) ∧ HasHeight (a.long.read j) T
  short : ∀ j,Reduced root.polynomial (a.short.read j) ∧ HasHeight (a.short.read j) T
  capacity : ∀ j,Reduced root.polynomial (a.capacity.read j) ∧ HasHeight (a.capacity.read j) T
  resource : ∀ j,Reduced root.polynomial (a.resource.read j) ∧ HasHeight (a.resource.read j) T

theorem endpoint_bounds (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T) (j : Fin 3) :
    Reduced root.polynomial (endpoint root a j) ∧ HasHeight (endpoint root a j) T := by
  unfold endpoint
  split
  · exact ha.long j
  · exact ha.short j

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T) :
    PlayerSpecificAlgebraicNestedParameterSizes.Fits root (prepare model root a).input (step T) := by
  have hi : T ≤ step T := (Nat.le_succ _).trans (large T)
  have first := endpoint_bounds root a T ha ((Equiv.swap (focus model root a) 2) 0)
  have second := endpoint_bounds root a T ha ((Equiv.swap (focus model root a) 2) 1)
  refine ⟨⟨ha.budget.1,mono ha.budget.2 hi⟩,⟨first.1,mono first.2 hi⟩,⟨second.1,mono second.2 hi⟩,
    ⟨(ha.long _).1,mono (ha.long _).2 hi⟩,⟨(ha.short _).1,mono (ha.short _).2 hi⟩,?_⟩
  exact ⟨PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0,
    divide_height root.polynomial _ _ T hm hm0 hml (ha.resource _).1 (ha.capacity _).1 hmT (ha.resource _).2 (ha.capacity _).2 hT⟩

end Blotto.PlayerSpecificAlgebraicNestedTerminalSizes
