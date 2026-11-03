import Blotto.GeneralPaperCircleThresholdRank
import Blotto.FiniteUniformPoints

/-! Erased finite averages and their actual scalar uniform laws. The
canonical half-tie formula uses both strict and weak events, including zero
atoms; it never replaces a half tie by a strict win or loss. -/
namespace Blotto.GeneralPaperCircleFiniteAverage
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def average {N : ℕ} (f : Fin N → ℝ) : ℝ := (∑ i,f i)/N

theorem average_le {N : ℕ} (f g : Fin N → ℝ) (h : ∀ i,f i≤g i) : average f≤average g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) (Nat.cast_nonneg N)

theorem average_add {N : ℕ} (f g : Fin N → ℝ) : average (fun i => f i+g i)=average f+average g := by
  unfold average
  rw [Finset.sum_add_distrib,add_div]

theorem average_mul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) : average (fun i => c*f i)=c*average f := by
  unfold average
  rw [←Finset.mul_sum]
  ring

theorem average_div {N : ℕ} (f : Fin N → ℝ) (c : ℝ) : average (fun i => f i/c)=average f/c := by
  unfold average
  rw [←Finset.sum_div]
  ring

theorem average_sum {N g : ℕ} (f : Fin g → Fin N → ℝ) :
    average (fun i => ∑ j,f j i)=∑ j,average (f j) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

theorem indicator_sum {N : ℕ} (p : Fin N → Prop) [DecidablePred p] :
    (∑ i,if p i then (1:ℝ) else 0)=((Finset.univ.filter p).card:ℝ) := by
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]

theorem average_indicator {N : ℕ} (p : Fin N → Prop) [DecidablePred p] :
    average (fun i => if p i then (1:ℝ) else 0)=((Finset.univ.filter p).card:ℝ)/N := by
  unfold average
  rw [indicator_sum]

theorem half_indicator (s t : ℝ) :
    share s t=((if t<s then (1:ℝ) else 0)+(if t≤s then 1 else 0))/2 := by
  rw [share_indicator]
  simp only [Set.indicator_apply,Set.mem_Iio,Set.mem_Iic]
  ring

theorem average_share {N : ℕ} (x : Fin N → ℝ) (t : ℝ) :
    average (fun i => share t (x i))=
      (((GeneralPaperCircleThresholdRank.strict x t:ℝ)/N)+((GeneralPaperCircleThresholdRank.weak x t:ℝ)/N))/2 := by
  simp_rw [half_indicator]
  rw [average_div,average_add,average_indicator,average_indicator]
  rfl

theorem average_permutation {N : ℕ} (f : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    average (fun i => f (π i))=average f := by
  unfold average
  rw [Equiv.sum_comp]

theorem average_rotation (D : ℕ) (hD : 0<D) (shift : ℕ) (f : Fin D → ℝ) :
    average (fun i:Fin D => f (GeneralPaperCircleCell.cell D hD shift i.val))=average f := by
  unfold average
  rw [GeneralPaperCircleFiniteSums.rotation D hD shift f]

theorem average_bins (R W : ℕ) (hR : 0<R) (hW : 0<W) (f : Fin R → ℝ) :
    average (fun i:Fin (R*W) => f (GeneralPaperCircleCell.bin R W hW i))=average f := by
  unfold average
  rw [GeneralPaperCircleFiniteSums.bins R W hW f]
  have hr : (R:ℝ)≠0 := by exact_mod_cast hR.ne'
  have hw : (W:ℝ)≠0 := by exact_mod_cast hW.ne'
  push_cast
  field_simp

theorem law_strict {N : ℕ} (hN : 0<N) (x : Fin N → ℝ) (t : ℝ) :
    (finiteUniformPoints hN x:Measure ℝ).real (Iio t)=(GeneralPaperCircleThresholdRank.strict x t:ℝ)/N := by
  rw [finiteUniformPoints_event hN x (Iio t) measurableSet_Iio]
  simp only [Set.mem_Iio,indicator_sum,GeneralPaperCircleThresholdRank.strict]

theorem law_weak {N : ℕ} (hN : 0<N) (x : Fin N → ℝ) (t : ℝ) :
    (finiteUniformPoints hN x:Measure ℝ).real (Iic t)=(GeneralPaperCircleThresholdRank.weak x t:ℝ)/N := by
  rw [finiteUniformPoints_event hN x (Iic t) measurableSet_Iic]
  simp only [Set.mem_Iic,indicator_sum,GeneralPaperCircleThresholdRank.weak]

theorem law_share {N : ℕ} (hN : 0<N) (x : Fin N → ℝ) (t : ℝ) :
    (∫ u,share t u ∂(finiteUniformPoints hN x:Measure ℝ))=average (fun i => share t (x i)) := by
  rw [integral_share,law_strict,law_weak,average_share]

end Blotto.GeneralPaperCircleFiniteAverage
