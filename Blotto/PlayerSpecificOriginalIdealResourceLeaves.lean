import Blotto.PlayerSpecificResourceIdealLeaves
import Blotto.PlayerSpecificAlgebraicPathContract

/-! Original accepted inputs certify every leaf of the exact native
resource semantics, including the same reached coefficient-height bound
already proved for every explicit Boolean path. -/
namespace Blotto.PlayerSpecificOriginalIdealResourceLeaves
open PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧ ∀ player,
      PlayerSpecificResourceIdealLeaves.ForLeaves RationalCostModel.schoolbook p
        (fun s => Valid p x s ∧ InBox (lengths p x) (eval s x) ∧
          (∑ j,eval s x j)=(if player then 2 else 2*(i.budget:ℝ)) ∧ s.active.length ≤ 1 ∧
          ∀ j,PlayerSpecificPolynomialHeights.HasHeight (s.data.read j)
            (PlayerSpecificAlgebraicPathContract.height N (PlayerSpecificInitialPositivePrecision.inputSize i)))
        (N-1) (start RationalCostModel.schoolbook p player) := by
  obtain ⟨x,hx,hpaths⟩ := PlayerSpecificAlgebraicPathContract.original_input i r hr
  refine ⟨x,hx,?_⟩
  intro player
  apply PlayerSpecificResourceIdealLeaves.of_paths
  intro choices
  have h := hpaths player choices
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2⟩

end Blotto.PlayerSpecificOriginalIdealResourceLeaves
