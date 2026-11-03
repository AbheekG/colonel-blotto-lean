import Blotto.WholeQuantileOrderCell
import Blotto.FiniteAnchorTransport

/-! Actual whole-law rational transport. The Borel row map first rounds
the same original allocation, then relabels each finite anchor. Equal old
anchors have equal new anchors by the checked signed cell. No label selector
or rational/uniform mixture weights are required. -/

namespace Blotto.WholeQuantileRationalTransport
open MeasureTheory Set RationalOrderCell WholeQuantileOrderCell
open scoped BigOperators Classical

noncomputable def oldAnchor {m : ℕ} (law : Mixed m) (K : ℕ) (field : Fin m) : Fin K → ℝ :=
  DeterministicQuantileRounding.anchor (marginal law field) K

def newAnchor {m K : ℕ} (coordinates : Coordinate m K → ℚ) (field : Fin m) (label : Fin K) : ℝ :=
  (rationalRow coordinates (fun _ => label) field : ℝ)

theorem label_orders {m K : ℕ} (law : Mixed m) (budgets : Fin 2 → ℚ)
    (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (field : Fin m) (left right : Fin K) :
    (oldAnchor law K field left < oldAnchor law K field right ↔
      newAnchor coordinates field left < newAnchor coordinates field right) ∧
    (oldAnchor law K field left = oldAnchor law K field right ↔
      newAnchor coordinates field left = newAnchor coordinates field right) := by
  have hp : (0 : ℝ) < coordinates none := by exact_mod_cast hMargin
  have h := field_order_preserved budgets (original law K) _ hCell hp field
    ⟨left.val,by omega⟩ ⟨right.val,by omega⟩
  change (_ ↔ _) ∧ (_ ↔ _) ∧ _ at h
  have ho (label : Fin K) :
      anchor (original law K) field ⟨label.val,by omega⟩ = oldAnchor law K field label :=
    original_label law K field label
  have hn (label : Fin K) :
      anchor (fun v => (coordinates (some v) : ℝ)) field ⟨label.val,by omega⟩ =
        newAnchor coordinates field label := (rationalRef_cast _ _).symm
  rw [ho left,ho right,hn left,hn right] at h
  exact ⟨h.1,h.2.1⟩

noncomputable def relabelRow {m K : ℕ} (law : Mixed m)
    (coordinates : Coordinate m K → ℚ) (row : Allocation m) : Allocation m :=
  fun field => FiniteAnchorTransport.relabel (oldAnchor law K field)
    (newAnchor coordinates field) (row field)

theorem relabelRow_measurable {m K : ℕ} (law : Mixed m) (coordinates : Coordinate m K → ℚ) :
    Measurable (relabelRow law coordinates) := by
  apply Measurable.of_eval
  intro field
  exact (FiniteAnchorTransport.relabel_measurable _ _).comp (measurable_pi_apply field)

theorem relabelRow_labelled {m K : ℕ} (law : Mixed m) (budgets : Fin 2 → ℚ)
    (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (labels : Fin m → Fin K) :
    relabelRow law coordinates (WholeQuantileRounding.labelledRow law K labels) =
      fun field => (rationalRow coordinates labels field : ℝ) := by
  funext field
  exact FiniteAnchorTransport.relabel_at_anchor _ _
    (fun i j hij => (label_orders law budgets coordinates hCell hMargin field i j).2.mp hij) (labels field)

noncomputable def transportRow {m K : ℕ} (law : Mixed m) (hK : 0 < K)
    (coordinates : Coordinate m K → ℚ) : Allocation m → Allocation m :=
  relabelRow law coordinates ∘ WholeQuantileRounding.roundRow law K hK

theorem transportRow_measurable {m K : ℕ} (law : Mixed m) (ownBudget : ℝ)
    (hBudget : ownBudget ≤ 1) (hLaw : Supported ownBudget law) (hK : 0 < K)
    (coordinates : Coordinate m K → ℚ) : Measurable (transportRow law hK coordinates) :=
  (relabelRow_measurable law coordinates).comp
    (WholeQuantileRounding.roundRow_measurable law ownBudget hBudget hLaw K hK)

theorem transportRow_feasible {m K : ℕ} (law : Mixed m) (hK : 0 < K)
    (budgets : Fin 2 → ℚ) (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (budget : Fin 2) (row : Allocation m)
    (hRow : Feasible (budgets budget : ℝ) row) :
    Feasible (budgets budget : ℝ) (transportRow law hK coordinates row) := by
  have hr := WholeQuantileRounding.roundRow_mem_finiteRows law K hK row
  obtain ⟨labels,_,he⟩ := Finset.mem_image.mp hr
  have hf := WholeQuantileRounding.roundRow_feasible law K hK (budgets budget : ℝ) row hRow
  rw [← he] at hf
  change Feasible _ (relabelRow law coordinates (WholeQuantileRounding.roundRow law K hK row))
  rw [← he,relabelRow_labelled law budgets coordinates hCell hMargin]
  apply rationalRow_feasible_of_original budgets (original law K) coordinates hCell hMargin labels budget
  rw [original_tuple_sum]
  exact hf.2

noncomputable def transportedLaw {m K : ℕ} (law : Mixed m) (hK : 0 < K)
    (coordinates : Coordinate m K → ℚ) : Mixed m := law.map (transportRow law hK coordinates)

theorem transportedLaw_supported {m K : ℕ} (law : Mixed m) (hK : 0 < K)
    (budgets : Fin 2 → ℚ) (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (budget : Fin 2)
    (hBudget : (budgets budget : ℝ) ≤ 1) (hLaw : Supported (budgets budget : ℝ) law) :
    Supported (budgets budget : ℝ) (transportedLaw law hK coordinates) := by
  change ∀ᵐ row ∂Measure.map (transportRow law hK coordinates) (law : Measure (Allocation m)), _
  apply (ae_map_iff (transportRow_measurable law _ hBudget hLaw hK coordinates).aemeasurable
    (measurable_feasible _)).mpr
  exact hLaw.mono fun row hr => transportRow_feasible law hK budgets coordinates hCell hMargin budget row hr

theorem transportedLaw_rounding {m K : ℕ} (law : Mixed m) (ownBudget : ℝ)
    (hBudget : ownBudget ≤ 1) (hLaw : Supported ownBudget law) (hK : 0 < K)
    (coordinates : Coordinate m K → ℚ) :
    transportedLaw law hK coordinates =
      (WholeQuantileRounding.roundedLaw law K hK).map (relabelRow law coordinates) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ (law : Measure (Allocation m)) = Measure.map _ (Measure.map _ (law : Measure (Allocation m)))
  rw [Measure.map_map (relabelRow_measurable law coordinates)
    (WholeQuantileRounding.roundRow_measurable law ownBudget hBudget hLaw K hK)]
  rfl

noncomputable def rationalRows {m K : ℕ} (coordinates : Coordinate m K → ℚ) : Finset (Allocation m) :=
  Finset.univ.image (fun labels : Fin m → Fin K => fun field => (rationalRow coordinates labels field : ℝ))

theorem rationalRows_card {m K : ℕ} (coordinates : Coordinate m K → ℚ) :
    (rationalRows coordinates).card ≤ K ^ m := by
  simpa only [rationalRows,Finset.card_univ,Fintype.card_fun,Fintype.card_fin] using
    (Finset.card_image_le (f := fun labels : Fin m → Fin K => fun field => (rationalRow coordinates labels field : ℝ))
      (s := Finset.univ))

theorem transportRow_mem_rationalRows {m K : ℕ} (law : Mixed m) (hK : 0 < K)
    (budgets : Fin 2 → ℚ) (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (row : Allocation m) :
    transportRow law hK coordinates row ∈ rationalRows coordinates := by
  obtain ⟨labels,_,he⟩ := Finset.mem_image.mp (WholeQuantileRounding.roundRow_mem_finiteRows law K hK row)
  change relabelRow law coordinates _ ∈ _
  rw [← he,relabelRow_labelled law budgets coordinates hCell hMargin]
  exact Finset.mem_image.mpr ⟨labels,Finset.mem_univ _,rfl⟩

theorem transportedLaw_finite_supported {m K : ℕ} (law : Mixed m) (hK : 0 < K)
    (budgets : Fin 2 → ℚ) (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (ownBudget : ℝ)
    (hBudget : ownBudget ≤ 1) (hLaw : Supported ownBudget law) :
    ∀ᵐ row ∂(transportedLaw law hK coordinates : Measure (Allocation m)),
      row ∈ (rationalRows coordinates : Set (Allocation m)) := by
  change ∀ᵐ row ∂Measure.map (transportRow law hK coordinates) (law : Measure (Allocation m)), _
  apply (ae_map_iff (transportRow_measurable law _ hBudget hLaw hK coordinates).aemeasurable
    (rationalRows coordinates).finite_toSet.measurableSet).mpr
  exact Filter.Eventually.of_forall (transportRow_mem_rationalRows law hK budgets coordinates hCell hMargin)

/-- Two separately supplied original whole draws remain independent under
the separate deterministic transports. Dependence within each row remains
the original whole-law dependence; no shared random preparation is averaged. -/
theorem transportedLaw_product {m K L : ℕ} (left right : Mixed m)
    (leftBudget rightBudget : ℝ) (hLeftBudget : leftBudget ≤ 1) (hRightBudget : rightBudget ≤ 1)
    (hLeft : Supported leftBudget left) (hRight : Supported rightBudget right)
    (hK : 0 < K) (hL : 0 < L)
    (leftCoordinates : Coordinate m K → ℚ) (rightCoordinates : Coordinate m L → ℚ) :
    Measure.map (Prod.map (transportRow left hK leftCoordinates) (transportRow right hL rightCoordinates))
      ((left : Measure (Allocation m)).prod (right : Measure (Allocation m))) =
      (transportedLaw left hK leftCoordinates : Measure (Allocation m)).prod
        (transportedLaw right hL rightCoordinates : Measure (Allocation m)) := by
  rw [← Measure.map_prod_map _ _
    (transportRow_measurable left leftBudget hLeftBudget hLeft hK leftCoordinates)
    (transportRow_measurable right rightBudget hRightBudget hRight hL rightCoordinates)]
  rfl

end Blotto.WholeQuantileRationalTransport
