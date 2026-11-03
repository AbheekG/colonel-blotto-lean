import Blotto.GeneralPaperSelectedCoordinatePayoff

/-! Actual finite uniform whole-row laws with the paper's selected shifts.
The same selected shift is used for every coordinate of a row. Canonical
continuous security increases by at most 1/S from the full-cell lift. -/
namespace Blotto.GeneralPaperSelectedCircleLaw
open MeasureTheory
open GeneralPaperCircleFiniteAverage GeneralPaperSelectedShift GeneralPaperCircleCanonicalLift
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

noncomputable def law {h g T : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hT : 0<T)
    (weights : Fin g → ℕ) (rows : Fin T → Allocation (h+R)) : Mixed (h+g) :=
  GeneralPaperUniformRowLaw.mixture hT (fun r => GeneralPaperUniformRowLaw.law hS
    (fun l:Fin S => row R W hR hW weights (rows r) (selected (R*W) S (Nat.mul_pos hR hW) hS l).val))

theorem row_payoff_bound {h g : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (v : Values (h+g)) (y : Allocation (h+g)) (x : Allocation (h+R)) :
    average (fun l:Fin S => payoff v y (row R W hR hW weights x (selected (R*W) S (Nat.mul_pos hR hW) hS l).val))≤
      average (fun c:Fin (R*W) => payoff v y (row R W hR hW weights x c.val))+1/(S:ℝ) := by
  have hδ : (0:ℝ)≤1/(S:ℝ) := by positivity
  have hCoord : ∀ j:Fin (h+g),
      average (fun l:Fin S => share (y j) (row R W hR hW weights x (selected (R*W) S (Nat.mul_pos hR hW) hS l).val j))≤
        average (fun c:Fin (R*W) => share (y j) (row R W hR hW weights x c.val j))+1/(S:ℝ) := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro a
      simp only [row,GeneralPaperCircleHardBudget.reconstruct_kept,
        average_const hS,average_const (Nat.mul_pos hR hW)]
      exact le_add_of_nonneg_right hδ
    · intro a
      simp only [row,GeneralPaperCircleHardBudget.reconstruct_light]
      have hw : weights a≤W := by
        rw [←hs]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      have he := GeneralPaperSelectedCoordinatePayoff.share_error R W S hR hW hS weights
        (GeneralPaperCircleSortedComparison.sorted (representatives x))
        (GeneralPaperCircleSortedComparison.sorted_monotone (representatives x)) a hw (y (Fin.natAdd h a))
      linarith only [he.2]
  unfold payoff
  rw [average_sum,average_sum]
  simp_rw [average_mul]
  calc
    _ ≤ ∑ j,v.weight j*(average (fun c:Fin (R*W) => share (y j) (row R W hR hW weights x c.val j))+1/(S:ℝ)) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hCoord j) (v.positive j).le)
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,v.normalized,one_mul]

theorem pure_bound {h g T : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hT : 0<T)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (rows : Fin T → Allocation (h+R))
    (v : Values (h+g)) (y : Allocation (h+g)) :
    purePayoff v y (law R W S hR hW hS hT weights rows)≤
      purePayoff v y (GeneralPaperCircleCanonicalLift.law R W hR hW hT weights rows)+1/(S:ℝ) := by
  unfold law GeneralPaperCircleCanonicalLift.law
  rw [GeneralPaperUniformRowLaw.pure_mixture,GeneralPaperUniformRowLaw.pure_mixture]
  simp_rw [GeneralPaperUniformRowLaw.pure_law]
  have he := average_le _ _ (fun r => row_payoff_bound R W S hR hW hS weights hs v y (rows r))
  rw [average_add,average_const hT] at he
  exact he

theorem security_bound {h g T : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hT : 0<T)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (rows : Fin T → Allocation (h+R))
    (v : Values (h+g)) (B : ℝ) (hB : 0≤B) :
    security v B (law R W S hR hW hS hT weights rows)≤
      security v B (GeneralPaperCircleCanonicalLift.law R W hR hW hT weights rows)+1/(S:ℝ) := by
  apply security_le v hB
  intro y hy
  exact (pure_bound R W S hR hW hS hT weights hs rows v y).trans
    (add_le_add (purePayoff_le_security v hy _) (le_refl (1/(S:ℝ))))

theorem supported {h g T : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hT : 0<T)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (rows : Fin T → Allocation (h+R)) (B : ℝ)
    (hRows : ∀ r,Feasible B (rows r)) : Supported B (law R W S hR hW hS hT weights rows) := by
  apply GeneralPaperUniformRowLaw.mixture_supported
  intro r
  apply GeneralPaperUniformRowLaw.law_supported
  intro l
  exact row_feasible R W hR hW weights hs (rows r) B (hRows r) _

theorem uniform_component_supported {n T : ℕ} (hT : 0<T) (laws : Fin T → Mixed n) (B : ℝ)
    (h : Supported B (GeneralPaperUniformRowLaw.mixture hT laws)) (r : Fin T) : Supported B (laws r) := by
  change ∀ᵐ x ∂Measure.sum (fun r:Fin T => ENNReal.ofReal (1/(T:ℝ)) • (laws r:Measure (Allocation n))),Feasible B x at h
  exact (Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (1/(T:ℝ))≠0)).mp
    (Measure.ae_sum_iff.mp h r)

theorem supported_of_full {h g T : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hT : 0<T)
    (weights : Fin g → ℕ) (rows : Fin T → Allocation (h+R)) (B : ℝ)
    (h : Supported B (GeneralPaperCircleCanonicalLift.law R W hR hW hT weights rows)) :
    Supported B (law R W S hR hW hS hT weights rows) := by
  apply GeneralPaperUniformRowLaw.mixture_supported
  intro r
  apply GeneralPaperUniformRowLaw.law_supported
  intro l
  have hr := uniform_component_supported hT _ B h r
  exact GeneralPaperUniformRowSupport.rows_feasible (Nat.mul_pos hR hW)
    (fun c:Fin (R*W) => row R W hR hW weights (rows r) c.val) B hr (selected (R*W) S (Nat.mul_pos hR hW) hS l)

end Blotto.GeneralPaperSelectedCircleLaw
