import Blotto.GeneralPaperFiniteRowSet
import Blotto.WholeQuantileRationalSecurity

/-! The retained whole-law rational quantile comparator is realized in the
actual closed code alphabet. Its original real probabilities, feasible rows
and continuous security bound are preserved, with no older source trainer.
The constructed alphabet denominator bound is discharged separately.
-/
namespace Blotto.GeneralPaperRationalComparator
open MeasureTheory
open scoped BigOperators Classical
open GeneralPaperCodeAlphabet RationalOrderCell WholeQuantileOrderCell WholeQuantileRationalTransport
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def rationalRowsQ {m K : ℕ} (coordinates : Coordinate m K → ℚ) : Finset (Fin m → ℚ) :=
  Finset.univ.image (rationalRow coordinates)

theorem exists_code_comparator {m : ℕ} (a : Alphabet) (v : Values m) (law : Mixed m)
    (budgets : Fin 2 → ℚ) (own opposing : Fin 2)
    (hOwn : (budgets own:ℝ)≤1) (hLaw : Supported (budgets own:ℝ) law) (hOpposing : 0≤(budgets opposing:ℝ))
    (K : ℕ) (hK : 0<K) (hD : commonDenominator budgets*(m+2)^(m*(K-1)+1)≤a.D) (qbar : ℕ) :
    ∃ X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false (budgets own),
      security v (budgets opposing:ℝ) (GeneralPaperCodeMixturePhysical.physicalLaw X qbar)≤
        security v (budgets opposing:ℝ) law+1/(K:ℝ) ∧
      ∃ s : Finset (Allocation m), s.card≤K^m ∧
        ∀ᵐ row ∂(GeneralPaperCodeMixturePhysical.physicalLaw X qbar:Measure (Allocation m)), row∈s := by
  obtain ⟨coordinates,denominator,hPositive,hBound,hDivides,hSupported,hCard,hFinite,hSecurity⟩ :=
    WholeQuantileRationalSecurity.exists_rational_comparator v law budgets own opposing hOwn hLaw hOpposing K hK
  let result := transportedLaw law hK coordinates
  have hSupport : ∀ᵐ row ∂(result:Measure (Allocation m)), ∃ r∈rationalRowsQ coordinates, row=(fun j => (r j:ℝ)) := by
    filter_upwards [hFinite] with row hr
    obtain ⟨labels,hl,he⟩ := Finset.mem_image.mp hr
    refine ⟨rationalRow coordinates labels,Finset.mem_image.mpr ⟨labels,Finset.mem_univ _,rfl⟩,he.symm⟩
  have hDen : ∀ r∈rationalRowsQ coordinates, ∀ j, (r j).den≤a.D := by
    intro r hr j
    obtain ⟨labels,hl,rfl⟩ := Finset.mem_image.mp hr
    have hd : (rationalRow coordinates labels j).den∣denominator := hDivides j (labels j)
    exact (Nat.le_of_dvd hPositive hd).trans (hBound.trans hD)
  obtain ⟨X,hX⟩ := GeneralPaperFiniteRowSet.realization a (budgets own) (by exact_mod_cast hOwn) result
    (rationalRowsQ coordinates) hSupported hSupport hDen qbar
  refine ⟨X,?_,rationalRows coordinates,hCard,?_⟩
  · rw [hX]
    exact hSecurity
  · rw [hX]
    exact hFinite

end Blotto.GeneralPaperRationalComparator
