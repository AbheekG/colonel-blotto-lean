import Blotto.PlayerSpecificAlgebraicNestedFirstSizes

/-! Proof-only widening and reduced-row views of the actual raw inputs. -/
namespace Blotto.PlayerSpecificAlgebraicNestedInputTools
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

theorem fits_mono (root : Candidate) (a : Input) (T U : ℕ) (h : Fits root a T) (hTU : T≤U) : Fits root a U :=
  ⟨⟨h.budget.1,mono h.budget.2 hTU⟩,⟨h.first.1,mono h.first.2 hTU⟩,⟨h.second.1,mono h.second.2 hTU⟩,
    ⟨h.long.1,mono h.long.2 hTU⟩,⟨h.short.1,mono h.short.2 hTU⟩,⟨h.probability.1,mono h.probability.2 hTU⟩⟩

theorem environment_reduced (root : Candidate) (a : Input) (extra : Data) (T : ℕ) (h : Fits root a T)
    (hExtra : Reduced root.polynomial extra) : ∀ j,Reduced root.polynomial ((environment a extra).read j) := by
  intro j
  fin_cases j <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact h.budget.1
  · exact h.first.1
  · exact h.second.1
  · exact h.long.1
  · exact h.short.1
  · exact h.probability.1
  · exact hExtra

end Blotto.PlayerSpecificAlgebraicNestedInputTools
