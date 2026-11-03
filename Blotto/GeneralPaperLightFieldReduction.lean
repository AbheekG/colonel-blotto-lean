import Blotto.GeneralPaperRoundedValueCanonical

/-! Mathematical specification of the paper's light-field reduction,
in original battlefield order. These definitions identify the values and
maps that the native classifier must return; they do not assert a native
classification price or the circle-lifting theorem. -/
namespace Blotto.GeneralPaperLightFieldReduction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def accuracy (k : ℕ) : ℚ := 1/(2:ℚ)^k
def representatives (k : ℕ) : ℕ := 8*2^k
def heavy {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => accuracy k/10<v.weight j)
def light {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => v.weight j≤accuracy k/10)
def mass {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : ℚ := ∑ j∈light v k,v.weight j
def count {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : ℕ :=
  (heavy v k).card+min (light v k).card (representatives k)

theorem accuracy_positive (k : ℕ) : 0<accuracy k := by unfold accuracy; positivity
theorem representatives_positive (k : ℕ) : 0<representatives k := by unfold representatives; positivity

theorem heavy_mem {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (j : Fin n) :
    j∈heavy v k ↔ accuracy k/10<v.weight j := by simp only [heavy,Finset.mem_filter,Finset.mem_univ,true_and]
theorem light_mem {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (j : Fin n) :
    j∈light v k ↔ v.weight j≤accuracy k/10 := by simp only [light,Finset.mem_filter,Finset.mem_univ,true_and]

theorem cardinalities {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) :
    (heavy v k).card+(light v k).card=n := by
  simpa only [heavy,light,not_lt,Finset.card_univ,Fintype.card_fin] using
    (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun j => accuracy k/10<v.weight j))

theorem masses {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) :
    (∑ j∈heavy v k,v.weight j)+mass v k=1 := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => accuracy k/10<v.weight j) v.weight
  simpa only [heavy,light,mass,not_lt,v.sum_one] using h

theorem mass_nonnegative {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : 0≤mass v k :=
  Finset.sum_nonneg (fun j _ => (v.positive j).le)

theorem mass_le_one {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : mass v k≤1 := by
  have h := masses v k
  have hh : 0≤∑ j∈heavy v k,v.weight j := Finset.sum_nonneg (fun j _ => (v.positive j).le)
  linarith only [h,hh]

theorem mass_positive {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (hl : 0<(light v k).card) :
    0<mass v k := Finset.sum_pos (fun j _ => v.positive j) (Finset.card_pos.mp hl)

theorem heavy_bound {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) :
    (heavy v k).card<10*2^k := by
  have ha := accuracy_positive k
  by_cases hh : (heavy v k).Nonempty
  · have hStrict : (∑ _j∈heavy v k,accuracy k/10)<∑ j∈heavy v k,v.weight j :=
      Finset.sum_lt_sum_of_nonempty hh (fun j hj => (heavy_mem v k j).mp hj)
    simp only [Finset.sum_const,nsmul_eq_mul] at hStrict
    have hMass := masses v k
    have hNonneg := mass_nonnegative v k
    have hCard : ((heavy v k).card:ℚ)<10/accuracy k := by
      apply (lt_div_iff₀ ha).mpr
      linarith only [hStrict,hMass,hNonneg]
    have he : (10:ℚ)/accuracy k=10*(2:ℚ)^k := by unfold accuracy; field_simp
    rw [he] at hCard
    exact_mod_cast hCard
  · have hz : (heavy v k).card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hh)
    rw [hz]
    positivity

theorem count_le_original {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : count v k≤n := by
  have h := cardinalities v k
  have hm := Nat.min_le_left (light v k).card (representatives k)
  unfold count
  omega

theorem count_bound {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : count v k<18*2^k := by
  have hh := heavy_bound v k
  have hm := Nat.min_le_right (light v k).card (representatives k)
  unfold count representatives at *
  omega

theorem count_positive {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) : 0<count v k := by
  have hn := v.fields_positive
  have hp := representatives_positive k
  have h := cardinalities v k
  unfold count
  omega

theorem count_no_replacement {n : ℕ} (v : RationalFieldSelector n) (k : ℕ)
    (h : (light v k).card≤representatives k) : count v k=n := by
  unfold count
  rw [Nat.min_eq_left h,cardinalities]

theorem count_replacement {n : ℕ} (v : RationalFieldSelector n) (k : ℕ)
    (h : representatives k<(light v k).card) : count v k=(heavy v k).card+representatives k := by
  unfold count
  rw [Nat.min_eq_right h.le]

theorem ordered_sum {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℚ) :
    (∑ i:Fin s.card,f (s.orderEmbOfFin rfl i))=∑ j∈s,f j := by
  have h := Finset.sum_map Finset.univ (s.orderEmbOfFin rfl).toEmbedding f
  rw [Finset.map_orderEmbOfFin_univ] at h
  exact h.symm

def replaced {n : ℕ} (v : RationalFieldSelector n) (k : ℕ)
    (h : representatives k<(light v k).card) : RationalFieldSelector ((heavy v k).card+representatives k) where
  weight := Fin.addCases (fun i => v.weight ((heavy v k).orderEmbOfFin rfl i)) (fun _ => mass v k/representatives k)
  positive := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [Fin.addCases_left] using v.positive ((heavy v k).orderEmbOfFin rfl i)
    · intro i
      simp only [Fin.addCases_right]
      exact div_pos (mass_positive v k (lt_trans (representatives_positive k) h))
        (by exact_mod_cast representatives_positive k)
  sum_one := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
    rw [ordered_sum]
    have hp : (representatives k:ℚ)≠0 := by exact_mod_cast (representatives_positive k).ne'
    rw [mul_div_cancel₀ _ hp]
    exact masses v k

theorem replaced_heavy {n : ℕ} (v : RationalFieldSelector n) (k : ℕ)
    (h : representatives k<(light v k).card) (i : Fin (heavy v k).card) :
    (replaced v k h).weight (Fin.castAdd (representatives k) i)=v.weight ((heavy v k).orderEmbOfFin rfl i) := by
  simp only [replaced,Fin.addCases_left]

theorem replaced_representative {n : ℕ} (v : RationalFieldSelector n) (k : ℕ)
    (h : representatives k<(light v k).card) (i : Fin (representatives k)) :
    (replaced v k h).weight (Fin.natAdd (heavy v k).card i)=mass v k/representatives k := by
  simp only [replaced,Fin.addCases_right]

theorem equal_representatives {n : ℕ} (v : RationalFieldSelector n) (k : ℕ)
    (h : representatives k<(light v k).card) (i j : Fin (representatives k)) :
    (replaced v k h).weight (Fin.natAdd (heavy v k).card i)=
      (replaced v k h).weight (Fin.natAdd (heavy v k).card j) := by
  rw [replaced_representative,replaced_representative]

theorem representative_bound {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) :
    mass v k/representatives k≤accuracy k/8 := by
  have h := div_le_div_of_nonneg_right (mass_le_one v k)
    (show (0:ℚ)≤representatives k by exact_mod_cast (representatives_positive k).le)
  have he : (1:ℚ)/representatives k=accuracy k/8 := by unfold representatives accuracy; push_cast; ring
  exact h.trans_eq he

theorem square_error {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) :
    (∑ j∈light v k,(v.weight j)^2)≤accuracy k/10*mass v k := by
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_right ((light_mem v k j).mp hj) (v.positive j).le
  nlinarith only [h]

theorem reconstruction_error {n : ℕ} (v : RationalFieldSelector n) (k : ℕ)
    (hl : 0<(light v k).card) :
    (∑ j∈light v k,(v.weight j)^2)/mass v k+mass v k/representatives k≤9*accuracy k/40 := by
  have hm := mass_positive v k hl
  have hs := (div_le_iff₀ hm).mpr (square_error v k)
  have hr := representative_bound v k
  linarith only [hs,hr]

end Blotto.GeneralPaperLightFieldReduction
