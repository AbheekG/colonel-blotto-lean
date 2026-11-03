import Blotto.GeneralPaperRowQuantizer

/-! CDF and continuous-security guarantees of the actual whole-row
quantizer. Counts use uniform original row occurrences, with no independent
field resampling. Both strict and weak thresholds include every real value.
-/
namespace Blotto.GeneralPaperRowQuantizer
open GeneralPaperDictionary MeasureTheory Set
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def frequency {T m K : ℕ} (d : Dictionary T m K) (j : Fin m)
    (P : ℚ → Prop) : ℝ :=
  ((Finset.univ.filter (fun i => P (d.anchor j (d.label i j)))).card:ℝ)/(T:ℝ)

theorem closed_count {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (j : Fin m) (t : ℝ) :
    closedCDF (law d hT).law j t=frequency d j (fun q => (q:ℝ)≤t) := by
  unfold closedCDF marginal
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic]
  change ((law d hT).law : Measure (Allocation m)).real {row | row j≤t}=_
  rw [(law d hT).law_event {row | row j≤t} (measurableSet_le (measurable_pi_apply j) measurable_const)]
  have hw (i : Fin T) : (law d hT).realWeight i=1/(T:ℝ) := by
    simp only [law,RationalWholeRowLaw.realWeight,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  have hr (i : Fin T) : (law d hT).realRow i j=(d.anchor j (d.label i j):ℝ) := rfl
  change (∑ i,(law d hT).realWeight i*(if (law d hT).realRow i j≤t then 1 else 0))=_
  simp only [hw,hr,frequency,mul_ite,mul_one,mul_zero,Finset.sum_ite,Finset.sum_const_zero,
    add_zero,Finset.sum_const,nsmul_eq_mul]
  ring

theorem strict_count {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (j : Fin m) (t : ℝ) :
    strictCDF (law d hT).law j t=frequency d j (fun q => (q:ℝ)<t) := by
  unfold strictCDF marginal
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [map_measureReal_apply (measurable_pi_apply j) measurableSet_Iio]
  change ((law d hT).law : Measure (Allocation m)).real {row | row j<t}=_
  rw [(law d hT).law_event {row | row j<t} (measurableSet_lt (measurable_pi_apply j) measurable_const)]
  have hw (i : Fin T) : (law d hT).realWeight i=1/(T:ℝ) := by
    simp only [law,RationalWholeRowLaw.realWeight,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  have hr (i : Fin T) : (law d hT).realRow i j=(d.anchor j (d.label i j):ℝ) := rfl
  change (∑ i,(law d hT).realWeight i*(if (law d hT).realRow i j<t then 1 else 0))=_
  simp only [hw,hr,frequency,mul_ite,mul_one,mul_zero,Finset.sum_ite,Finset.sum_const_zero,
    add_zero,Finset.sum_const,nsmul_eq_mul]
  ring

theorem row_event_upper {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (j : Fin m)
    (P : ℚ → Prop) [DecidablePred P] (hDown : ∀ a b,a≤b → P b → P a) :
    (Finset.univ.filter (fun i => P ((build hK hB rows).anchor j ((build hK hB rows).label i j)))).card ≤
      (Finset.univ.filter (fun i => P ((rows.read i).read j))).card+B := by
  have h := GeneralPaperQuantizedColumn.bid_event_upper hK hB (columnInput rows j) P hDown
  have hNew (i : Fin (K*B)) :
      (build hK hB rows).anchor j ((build hK hB rows).label i j)=
        GeneralPaperQuantizedColumn.bid (GeneralPaperQuantizedColumn.build hK hB (columnInput rows j)) i := by
    simp only [build,dictionary,prepare,FixedArrayTable.read_ofFn,GeneralPaperQuantizedColumn.bid]
  have hSource (i : Fin (K*B)) : (columnInput rows j).read i=(rows.read i).read j :=
    FixedArrayTable.read_ofFn _ _
  simpa only [← hNew,hSource] using h

theorem row_event_lower {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j)
    (j : Fin m) (P : ℚ → Prop) [DecidablePred P] (hDown : ∀ a b,a≤b → P b → P a) :
    (Finset.univ.filter (fun i => P ((rows.read i).read j))).card ≤
      (Finset.univ.filter (fun i => P ((build hK hB rows).anchor j ((build hK hB rows).label i j)))).card := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hDown _ _ (row_coordinate_le hK hB rows hRows i j)
    (Finset.mem_filter.mp hi).2⟩

theorem frequency_bounds {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j)
    (j : Fin m) (P : ℚ → Prop) (hDown : ∀ a b,a≤b → P b → P a) :
    frequency (original rows) j P ≤ frequency (build hK hB rows) j P ∧
      frequency (build hK hB rows) j P ≤ frequency (original rows) j P+1/(K:ℝ) := by
  have hT : (0:ℝ)<(K*B:ℕ) := by exact_mod_cast Nat.mul_pos hK hB
  have hLower := row_event_lower hK hB rows hRows j P hDown
  have hUpper := row_event_upper hK hB rows j P hDown
  have hl : ((Finset.univ.filter (fun i => P ((rows.read i).read j))).card:ℝ) ≤
      (Finset.univ.filter (fun i => P ((build hK hB rows).anchor j ((build hK hB rows).label i j)))).card := by
    exact_mod_cast hLower
  have hu : ((Finset.univ.filter (fun i => P ((build hK hB rows).anchor j ((build hK hB rows).label i j)))).card:ℝ) ≤
      (Finset.univ.filter (fun i => P ((rows.read i).read j))).card+(B:ℝ) := by
    exact_mod_cast hUpper
  have hFrac : (B:ℝ)/(K*B:ℕ)=1/(K:ℝ) := by
    have hk : (K:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hK
    have hb : (B:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hB
    simp only [Nat.cast_mul]
    field_simp
  have hlo := div_le_div_of_nonneg_right hl hT.le
  have hhi := div_le_div_of_nonneg_right hu hT.le
  rw [add_div,hFrac] at hhi
  exact ⟨hlo,hhi⟩

theorem closed_bounds {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j)
    (j : Fin m) (t : ℝ) :
    closedCDF (law (original rows) (Nat.mul_pos hK hB)).law j t ≤
      closedCDF (law (build hK hB rows) (Nat.mul_pos hK hB)).law j t ∧
    closedCDF (law (build hK hB rows) (Nat.mul_pos hK hB)).law j t ≤
      closedCDF (law (original rows) (Nat.mul_pos hK hB)).law j t+1/(K:ℝ) := by
  simp only [closed_count]
  apply frequency_bounds hK hB rows hRows j
  intro a b hab hb
  have h : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  exact h.trans hb

theorem strict_bounds {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j)
    (j : Fin m) (t : ℝ) :
    strictCDF (law (original rows) (Nat.mul_pos hK hB)).law j t ≤
      strictCDF (law (build hK hB rows) (Nat.mul_pos hK hB)).law j t ∧
    strictCDF (law (build hK hB rows) (Nat.mul_pos hK hB)).law j t ≤
      strictCDF (law (original rows) (Nat.mul_pos hK hB)).law j t+1/(K:ℝ) := by
  simp only [strict_count]
  apply frequency_bounds hK hB rows hRows j
  intro a b hab hb
  have h : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  exact h.trans_lt hb

theorem cdf_close {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j) :
    CDFClose (law (build hK hB rows) (Nat.mul_pos hK hB)).law
      (law (original rows) (Nat.mul_pos hK hB)).law (1/(K:ℝ)) := by
  intro j t
  have h := closed_bounds hK hB rows hRows j t
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith only [h.2]

theorem security_bound {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j)
    (v : Values m) (budget : ℝ) (hBudget : 0≤budget) :
    security v budget (law (build hK hB rows) (Nat.mul_pos hK hB)).law ≤
      security v budget (law (original rows) (Nat.mul_pos hK hB)).law+1/(K:ℝ) := by
  have h := (abs_le.mp (security_close v hBudget (cdf_close hK hB rows hRows))).2
  linarith only [h]

end Blotto.GeneralPaperRowQuantizer
