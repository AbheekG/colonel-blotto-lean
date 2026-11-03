import Blotto.GeneralPaperCandidateBidSet

/-! Universal candidate lemma for the selected alphabet, with one alphabet
fixed before the rational budget ratio or unknown whole law is selected.
Real joint probabilities and hard at-most budgets are retained. -/
namespace Blotto.GeneralPaperUniversalCandidateComparator
open MeasureTheory
open GeneralPaperCodeAlphabet GeneralPaperCodeMixturePhysical GeneralPaperCandidateBidSet
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem common_den_divides (budgets : Fin 2 → ℚ) (i : Fin 2) :
    (budgets i).den ∣ RationalOrderCell.commonDenominator budgets := by
  fin_cases i <;> simp [RationalOrderCell.commonDenominator]

theorem every_whole_law {m : ℕ} (k qbar : ℕ) (hq : 0 < qbar) (hm : 0 < m) (v : Values m)
    (budgets : Fin 2 → ℚ) (own opposing : Fin 2)
    (hOne : (budgets own : ℝ) ≤ 1) (hOpposing : 0 ≤ (budgets opposing : ℝ))
    (hDen : RationalOrderCell.commonDenominator budgets ≤ qbar)
    (law : Mixed m) (hLaw : Supported (budgets own : ℝ) law) :
    ∃ X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m)
        (GeneralPaperComparatorParameters.alphabet m k qbar hq) false (budgets own),
      Supported (budgets own : ℝ) (physicalLaw X qbar) ∧
      (∀ᵐ row ∂(physicalLaw X qbar : Measure (Allocation m)),
        ∀ j,∃ bid ∈ bids (GeneralPaperComparatorParameters.alphabet m k qbar hq),row j = (bid : ℝ)) ∧
      security v (budgets opposing : ℝ) (physicalLaw X qbar) ≤
        security v (budgets opposing : ℝ) law + ((GeneralPaperSourceParameters.prepare k).z : ℝ) / 64 := by
  let a := GeneralPaperComparatorParameters.alphabet m k qbar hq
  have hD := GeneralPaperComparatorParameters.denominator_cap m k
    (RationalOrderCell.commonDenominator budgets) qbar hq hDen
  obtain ⟨X,hCompare,_⟩ := GeneralPaperRationalComparator.exists_code_comparator a v law budgets own opposing
    hOne hLaw hOpposing (GeneralPaperComparatorParameters.countRun k).power
    (GeneralPaperComparatorParameters.count_positive k) hD qbar
  rw [GeneralPaperComparatorParameters.count_error] at hCompare
  exact ⟨X,GeneralPaperCodeMixturePhysical.supported a false (budgets own) X
    (RationalOrderCell.commonDenominator budgets) qbar hm (RationalOrderCell.commonDenominator_positive budgets)
    hDen (common_den_divides budgets own),law_coordinates a (budgets own) X qbar,hCompare⟩

def budgets (ratio : ℚ) : Fin 2 → ℚ := ![1,ratio]

theorem budgets_den (ratio : ℚ) : RationalOrderCell.commonDenominator (budgets ratio) = ratio.den := by
  simp [budgets,RationalOrderCell.commonDenominator]

theorem all_ratios {m : ℕ} (k qbar : ℕ) (hq : 0 < qbar) (hm : 0 < m) (v : Values m) :
    ∀ (ratio : ℚ),0 < ratio → ratio < 1 → ratio.den ≤ qbar →
      ∀ (own opposing : Fin 2) (law : Mixed m),Supported (budgets ratio own : ℝ) law →
        ∃ X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m)
            (GeneralPaperComparatorParameters.alphabet m k qbar hq) false (budgets ratio own),
          Supported (budgets ratio own : ℝ) (physicalLaw X qbar) ∧
          (∀ᵐ row ∂(physicalLaw X qbar : Measure (Allocation m)),
            ∀ j,∃ bid ∈ bids (GeneralPaperComparatorParameters.alphabet m k qbar hq),row j = (bid : ℝ)) ∧
          security v (budgets ratio opposing : ℝ) (physicalLaw X qbar) ≤
            security v (budgets ratio opposing : ℝ) law + ((GeneralPaperSourceParameters.prepare k).z : ℝ) / 64 := by
  intro ratio hPositive hStrict hDen own opposing law hLaw
  have hOne : (budgets ratio own : ℝ) ≤ 1 := by
    fin_cases own
    · norm_num [budgets]
    · simp only [budgets]
      exact_mod_cast hStrict.le
  have hOpposing : 0 ≤ (budgets ratio opposing : ℝ) := by
    fin_cases opposing
    · norm_num [budgets]
    · simp only [budgets]
      exact_mod_cast hPositive.le
  exact every_whole_law k qbar hq hm v (budgets ratio) own opposing hOne hOpposing
    (by rwa [budgets_den]) law hLaw

theorem finite_set_statement {m : ℕ} (k qbar : ℕ) (hq : 0 < qbar) (hm : 0 < m) (v : Values m) :
    ∃ alphabet : Finset ℚ,(0 : ℚ) ∈ alphabet ∧ (1 : ℚ) ∈ alphabet ∧
      (∀ bid ∈ alphabet,0 ≤ bid ∧ bid ≤ 1 ∧ rationalWordWidth bid ≤
        1 + 2 * ((GeneralPaperComparatorParameters.alphabet m k qbar hq).lambda + 1)) ∧
      ∀ (ratio : ℚ),0 < ratio → ratio < 1 → ratio.den ≤ qbar →
        ∀ (own opposing : Fin 2) (law : Mixed m),Supported (budgets ratio own : ℝ) law →
          ∃ replacement : Mixed m,Supported (budgets ratio own : ℝ) replacement ∧
            (∀ᵐ row ∂(replacement : Measure (Allocation m)),∀ j,∃ bid ∈ alphabet,row j = (bid : ℝ)) ∧
            security v (budgets ratio opposing : ℝ) replacement ≤
              security v (budgets ratio opposing : ℝ) law + ((GeneralPaperSourceParameters.prepare k).z : ℝ) / 64 := by
  let a := GeneralPaperComparatorParameters.alphabet m k qbar hq
  refine ⟨bids a,zero_mem a,one_mem a,?_,?_⟩
  · intro bid hb
    exact ⟨(unit a bid hb).1,(unit a bid hb).2,rationalWordWidth_of_height (height a bid hb)⟩
  · intro ratio hPositive hStrict hDen own opposing law hLaw
    obtain ⟨X,hSupport,hCoordinates,hSecurity⟩ := all_ratios k qbar hq hm v ratio hPositive hStrict hDen own opposing law hLaw
    exact ⟨physicalLaw X qbar,hSupport,hCoordinates,hSecurity⟩

end Blotto.GeneralPaperUniversalCandidateComparator
