import Blotto.PlayerSpecificTerminalCoreCDF
import Blotto.PlayerSpecificAlgebraicLeafValues
import Blotto.ProportionalCDF

/-! Marginals of the actual direct proportional leaf map. A group
coordinate is scaled once; the fractional coordinate is copied once;
an absent coordinate is exactly zero. -/
namespace Blotto.PlayerSpecificLeafMapLaw
open MeasureTheory PlayerSpecificAlgebraicLeafAssignments PlayerSpecificAlgebraicLeafValues
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem measurable_point {N m : ℕ} (G : ProportionalGroups N m) (fractional : Option (Fin N)) :
    Measurable (point G fractional) := by
  apply Measurable.of_eval
  intro j
  have hm : Measurable (fun y : Allocation 4 => G.split (fun g => y (slot g)) j) :=
    ((measurable_pi_apply j).comp G.measurable_split).comp
      (Measurable.of_eval (fun g => measurable_pi_apply (slot g)))
  cases fractional with
  | none => simpa only [point,add_zero] using hm
  | some k =>
    by_cases hj : j=k
    · have hsum : Measurable (fun y : Allocation 4 => G.split (fun g => y (slot g)) j+y 3) :=
        hm.add (measurable_pi_apply 3)
      simpa only [point,hj,ite_true] using hsum
    · simpa only [point,hj,ite_false,add_zero] using hm

theorem group_point {N m : ℕ} (G : ProportionalGroups N m) (fractional : Option (Fin N))
    (hp : ∀ k,fractional=some k → ∀ g,k ∉ G.members g) (g : Fin m) (j : Fin N) (hj : j ∈ G.members g) (y : Allocation 4) :
    point G fractional y j=G.length j/G.total g*y (slot g) := by
  unfold point
  rw [G.split_group_coordinate hj]
  cases fractional with
  | none => exact add_zero _
  | some k =>
    have hn : j≠k := by intro he; subst j; exact hp k rfl g hj
    simp only [ite_eq_right hn,add_zero]

theorem pivot_point {N m : ℕ} (G : ProportionalGroups N m) (k : Fin N)
    (hp : ∀ g,k ∉ G.members g) (y : Allocation 4) : point G (some k) y k=y 3 := by
  rw [point,G.split_inactive_coordinate hp]
  simp

theorem group_marginal {N m : ℕ} (G : ProportionalGroups N m) (fractional : Option (Fin N))
    (hp : ∀ k,fractional=some k → ∀ g,k ∉ G.members g) (g : Fin m) (j : Fin N) (hj : j ∈ G.members g) (l : Mixed 4) :
    (marginal (l.map (point G fractional)) j : Measure ℝ)=
      Measure.map (fun t => G.length j/G.total g*t) (marginal l (slot g) : Measure ℝ) := by
  change Measure.map (fun y : Allocation N => y j) (Measure.map (point G fractional) (l : Measure (Allocation 4)))=
    Measure.map (fun t => G.length j/G.total g*t) (Measure.map (fun y : Allocation 4 => y (slot g)) (l : Measure (Allocation 4)))
  rw [Measure.map_map (measurable_pi_apply j) (measurable_point G fractional),
    Measure.map_map (g := fun t : ℝ => G.length j/G.total g*t)
      (measurable_const.mul measurable_id) (measurable_pi_apply (slot g))]
  congr 1
  funext y
  exact group_point G fractional hp g j hj y

theorem pivot_marginal {N m : ℕ} (G : ProportionalGroups N m) (k : Fin N)
    (hp : ∀ g,k ∉ G.members g) (l : Mixed 4) : marginal (l.map (point G (some k))) k=marginal l 3 := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun y : Allocation N => y k) (Measure.map (point G (some k)) (l : Measure (Allocation 4)))=_
  rw [Measure.map_map (measurable_pi_apply k) (measurable_point G (some k))]
  congr 1
  funext y
  exact pivot_point G k hp y

theorem group_CDF {N m : ℕ} (G : ProportionalGroups N m) (fractional : Option (Fin N))
    (hp : ∀ k,fractional=some k → ∀ g,k ∉ G.members g) (g : Fin m) (j : Fin N) (hj : j ∈ G.members g) (l : Mixed 4) (E : ℝ)
    (h : RealCDFClose (marginal l (slot g)) (uniformMarginal (G.total g) (G.total_pos g)) E) (z : ℝ) :
    |closedCDF (l.map (point G fractional)) j z-(Blotto.uniformLaw (G.length j)).real (Set.Iic z)| ≤ E := by
  have hs := h.scale (G.length j/G.total g) z
  change |(Measure.map (fun t => G.length j/G.total g*t) (marginal l (slot g) : Measure ℝ)).real (Set.Iic z)-
    (Measure.map (fun t => G.length j/G.total g*t) (Blotto.uniformLaw (G.total g))).real (Set.Iic z)| ≤ E at hs
  have hu : Measure.map (fun t : ℝ => G.length j/G.total g*t) (Blotto.uniformLaw (G.total g))=Blotto.uniformLaw (G.length j) :=
    scale_uniformLaw (G.length_pos j) (G.total_pos g)
  rw [hu] at hs
  unfold closedCDF
  rw [group_marginal G fractional hp g j hj l]
  exact hs

end Blotto.PlayerSpecificLeafMapLaw
