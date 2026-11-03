import Blotto.GeneralPaperDivisibleQuantizer
import Blotto.BudgetScalingRegret

/-! Materialized dictionary normalization. Scale all m*K rational anchors
once and retain exactly the same whole-row labels. The law is the common
positive change of units, including ties and arbitrary continuous deviations.
-/
namespace Blotto.GeneralPaperDictionary
open MeasureTheory
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

def scale {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) : Dictionary T m K :=
  let anchors := FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun l => c*d.anchor j l))
  ⟨d.label,fun j l => (anchors.read j).read l⟩

theorem scale_label {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (i : Fin T) (j : Fin m) :
    (scale d c).label i j=d.label i j := rfl

theorem scale_anchor {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (j : Fin m) (l : Fin K) :
    (scale d c).anchor j l=c*d.anchor j l := by
  simp only [scale,FixedArrayTable.read_ofFn]

theorem scale_balanced {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (h : Balanced d) :
    Balanced (scale d c) := h

theorem scale_zero {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (hK : 0<K)
    (h : ∀ j,d.anchor j ⟨0,hK⟩=0) (j : Fin m) : (scale d c).anchor j ⟨0,hK⟩=0 := by
  rw [scale_anchor,h,mul_zero]

theorem scale_nonnegative {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (hc : 0≤c)
    (h : ∀ j l,0≤d.anchor j l) (j : Fin m) (l : Fin K) : 0≤(scale d c).anchor j l := by
  rw [scale_anchor]
  exact mul_nonneg hc (h j l)

theorem scale_ordered {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (hc : 0≤c)
    (h : ∀ j,Monotone (d.anchor j)) (j : Fin m) : Monotone ((scale d c).anchor j) := by
  intro a b hab
  rw [scale_anchor,scale_anchor]
  exact mul_le_mul_of_nonneg_left (h j hab) hc

theorem scale_realRow {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (hT : 0<T) (i : Fin T) :
    (law (scale d c) hT).realRow i=scaleAllocation (c:ℝ) ((law d hT).realRow i) := by
  funext j
  change ((scale d c).anchor j ((scale d c).label i j):ℝ)=(c:ℝ)*(d.anchor j (d.label i j):ℝ)
  rw [scale_label,scale_anchor,Rat.cast_mul]

theorem scale_law {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (hT : 0<T) :
    (law (scale d c) hT).law=scaleLaw (c:ℝ) (law d hT).law := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((law (scale d c) hT).law : Measure (Allocation m)).real E=
    (scaleLaw (c:ℝ) (law d hT).law : Measure (Allocation m)).real E
  rw [(law (scale d c) hT).law_event E hE]
  change _=(Measure.map (scaleAllocation (c:ℝ)) ((law d hT).law : Measure (Allocation m))).real E
  rw [map_measureReal_apply (measurable_scaleAllocation (c:ℝ)) hE]
  rw [(law d hT).law_event _ (hE.preimage (measurable_scaleAllocation (c:ℝ)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [scale_realRow]
  rfl

theorem scale_rows_feasible {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (hc : 0≤c)
    (hT : 0<T) (budget : ℝ) (hRows : ∀ i,Feasible budget ((law d hT).realRow i)) (i : Fin T) :
    Feasible ((c:ℝ)*budget) ((law (scale d c) hT).realRow i) := by
  rw [scale_realRow]
  have hcr : (0:ℝ)≤c := by exact_mod_cast hc
  exact scaleAllocation_feasible hcr (hRows i)

theorem scale_security {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (hc : 0<c)
    (hT : 0<T) (v : Values m) (opposingBudget : ℝ) :
    security v ((c:ℝ)*opposingBudget) (law (scale d c) hT).law=
      security v opposingBudget (law d hT).law := by
  rw [scale_law]
  have hcr : (0:ℝ)<c := by exact_mod_cast hc
  exact security_scale v hcr opposingBudget _

def normalize {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ) : Dictionary T m K :=
  scale d budget⁻¹

theorem normalized_rows_feasible {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ)
    (hBudget : 0<budget) (hT : 0<T)
    (hRows : ∀ i,Feasible (budget:ℝ) ((law d hT).realRow i)) (i : Fin T) :
    Feasible 1 ((law (normalize d budget) hT).realRow i) := by
  have hb : (budget:ℝ)≠0 := by exact_mod_cast ne_of_gt hBudget
  have h := scale_rows_feasible d budget⁻¹ (inv_nonneg.mpr hBudget.le) hT (budget:ℝ) hRows i
  simpa only [normalize,Rat.cast_inv,inv_mul_cancel₀ hb] using h

theorem normalized_supported {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ)
    (hBudget : 0<budget) (hT : 0<T) (hRows : ∀ i,Feasible (budget:ℝ) ((law d hT).realRow i)) :
    Supported 1 (law (normalize d budget) hT).law :=
  RationalWholeRowLaw.law_supported _ 1 (normalized_rows_feasible d budget hBudget hT hRows)

theorem normalized_security {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ)
    (hBudget : 0<budget) (hT : 0<T) (v : Values m) (opposingBudget : ℝ) :
    security v (opposingBudget/(budget:ℝ)) (law (normalize d budget) hT).law=
      security v opposingBudget (law d hT).law := by
  have h := scale_security d budget⁻¹ (inv_pos.mpr hBudget) hT v opposingBudget
  simpa only [normalize,Rat.cast_inv,div_eq_mul_inv,mul_comm] using h

theorem label_occurs {T m K : ℕ} (d : Dictionary T m K) (hK : 0<K) (h : Balanced d)
    (j : Fin m) (l : Fin K) : ∃ i,d.label i j=l := by
  by_contra! hn
  have hz : labelMass d j l=0 := by simp [labelMass,hn]
  rw [h j l] at hz
  have hp : (0:ℝ)<1/(K:ℝ) := by positivity
  linarith only [hz,hp]

theorem normalized_anchor_bounds {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ)
    (hBudget : 0<budget) (hT : 0<T) (hK : 0<K) (hBalanced : Balanced d)
    (hRows : ∀ i,Feasible (budget:ℝ) ((law d hT).realRow i)) (j : Fin m) (l : Fin K) :
    0≤(normalize d budget).anchor j l ∧ (normalize d budget).anchor j l≤1 := by
  obtain ⟨i,hi⟩ := label_occurs d hK hBalanced j l
  have hr := normalized_rows_feasible d budget hBudget hT hRows i
  have hn := hr.1 j
  have hu : (law (normalize d budget) hT).realRow i j≤1 :=
    (Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hr.1 k) (Finset.mem_univ j)).trans hr.2
  change (0:ℝ)≤((normalize d budget).anchor j (d.label i j):ℝ) at hn
  change ((normalize d budget).anchor j (d.label i j):ℝ)≤1 at hu
  rw [hi] at hn hu
  constructor
  · exact_mod_cast hn
  · exact_mod_cast hu

end Blotto.GeneralPaperDictionary
