import Blotto.GeneralPaperUniversalCandidateComparator
import Blotto.GeneralPaperContinuousResponsePayoff
import Blotto.GeneralPaperPhysicalBidExecution

/-! One finite feasible physical response set represents every continuous
deviation against all closed candidate laws simultaneously. The finite
maximum therefore equals the canonical continuous security supremum. -/
namespace Blotto.GeneralPaperFiniteContinuousResponses
open MeasureTheory
open GeneralPaperCodeAlphabet GeneralPaperCodeMixturePhysical
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2800000

def row {m : ℕ} (a : Alphabet) (qbar : ℕ) (codes : Fin m → Fin (2 ^ a.lambda)) : Allocation m :=
  fun j => ((GeneralPaperPhysicalBidExecution.decodedChoice a (codes j).val).physical
    (GeneralPaperTagBudgetTransfer.shift m qbar a.C) : ℝ)

noncomputable def responses (m : ℕ) (a : Alphabet) (B : ℚ) (qbar : ℕ) : Finset (Allocation m) :=
  (Finset.univ.image (row (m:=m) a qbar)).filter (Blotto.Feasible (B : ℝ))

theorem feasible {m : ℕ} (a : Alphabet) (B : ℚ) (qbar : ℕ) (y : Allocation m)
    (hy : y ∈ responses m a B qbar) : Blotto.Feasible (B : ℝ) y := (Finset.mem_filter.mp hy).2

theorem physical_mem {m : ℕ} (a : Alphabet) (B : ℚ) (hOne : B ≤ 1) (y : Allocation m)
    (hy : Blotto.Feasible (B : ℝ) y) (q qbar : ℕ) (hm : 0 < m) (hq : 0 < q) (hCap : q ≤ qbar) (hDen : B.den ∣ q) :
    GeneralPaperContinuousResponseMixture.physicalRow a B hOne y hy qbar ∈ responses m a B qbar := by
  let codes : Fin m → Fin (2 ^ a.lambda) := fun j =>
    ⟨(GeneralPaperContinuousResponseRow.codes a B hOne y hy).read j,
      GeneralPaperContinuousResponseRow.code_bound a B hOne y hy j⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨codes,Finset.mem_univ _,?_⟩,
    GeneralPaperContinuousResponseMixture.physicalRow_feasible a B hOne y hy q qbar hm hq hCap hDen⟩
  funext j
  dsimp only [row,codes,GeneralPaperContinuousResponseMixture.physicalRow]
  rw [GeneralPaperPhysicalBidExecution.decoded_choice_of_some a _ _
    (GeneralPaperContinuousResponseRow.decoded a B hOne y hy j)]

theorem representation {m : ℕ} (a : Alphabet) (B : ℚ) (hOne : B ≤ 1) (y : Allocation m)
    (hy : Blotto.Feasible (B : ℝ) y) (q qbar : ℕ) (hm : 0 < m) (hq : 0 < q) (hCap : q ≤ qbar) (hDen : B.den ∣ q) :
    ∃ replacement ∈ responses m a B qbar,∀ (v : Values m) (BX : ℚ)
      (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) (l : Fin X.law.labels),
        payoff v y (allocation X qbar l) = payoff v replacement (allocation X qbar l) :=
  ⟨GeneralPaperContinuousResponseMixture.physicalRow a B hOne y hy qbar,
    physical_mem a B hOne y hy q qbar hm hq hCap hDen,
    fun v BX X l => GeneralPaperContinuousResponseMixture.payoff_exact a BX B hOne y hy X qbar hm (by omega) v l⟩

theorem security_eq_finite_max {m : ℕ} (a : Alphabet) (B : ℚ) (hBudget : 0 ≤ B) (hOne : B ≤ 1)
    (q qbar : ℕ) (hm : 0 < m) (hq : 0 < q) (hCap : q ≤ qbar) (hDen : B.den ∣ q)
    (v : Values m) (BX : ℚ) (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) :
    ∃ best ∈ responses m a B qbar,
      security v (B : ℝ) (physicalLaw X qbar) = purePayoff v best (physicalLaw X qbar) ∧
      ∀ y ∈ responses m a B qbar,purePayoff v y (physicalLaw X qbar) ≤ purePayoff v best (physicalLaw X qbar) := by
  have hB : (0 : ℝ) ≤ B := by exact_mod_cast hBudget
  have hZero := feasible_zero (n:=m) hB
  have hNonempty : (responses m a B qbar).Nonempty :=
    ⟨_,physical_mem a B hOne (fun _ => 0) hZero q qbar hm hq hCap hDen⟩
  obtain ⟨best,hBest,hMax⟩ := Finset.exists_max_image (responses m a B qbar)
    (fun y => purePayoff v y (physicalLaw X qbar)) hNonempty
  refine ⟨best,hBest,le_antisymm ?_ (purePayoff_le_security v (feasible a B qbar best hBest) (physicalLaw X qbar)),hMax⟩
  apply security_le v hB (physicalLaw X qbar)
  intro y hy
  have hMem := physical_mem a B hOne y hy q qbar hm hq hCap hDen
  rw [GeneralPaperContinuousResponsePayoff.purePayoff_exact a BX B hOne y hy X qbar hm (by omega) v]
  exact hMax _ hMem

theorem every_bounded_denominator_budget {m : ℕ} (a : Alphabet) (qbar : ℕ) (hm : 0 < m)
    (B : ℚ) (hBudget : 0 ≤ B) (hOne : B ≤ 1) (hDen : B.den ≤ qbar)
    (v : Values m) (BX : ℚ) (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) :
    ∃ best ∈ responses m a B qbar,
      security v (B : ℝ) (physicalLaw X qbar) = purePayoff v best (physicalLaw X qbar) ∧
      ∀ y ∈ responses m a B qbar,purePayoff v y (physicalLaw X qbar) ≤ purePayoff v best (physicalLaw X qbar) :=
  security_eq_finite_max a B hBudget hOne B.den qbar hm B.den_pos hDen (dvd_refl _) v BX X

end Blotto.GeneralPaperFiniteContinuousResponses
