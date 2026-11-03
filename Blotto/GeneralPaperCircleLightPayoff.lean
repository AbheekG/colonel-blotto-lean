import Blotto.GeneralPaperCircleCoordinatePayoff

/-! The first light-field lifting loss, with one common shift and complete
row coupling preserved. The subsequent independent lower-quantile/cyclic
deviation comparison is still required for a reduced security bound. -/
namespace Blotto.GeneralPaperCircleLightPayoff
open GeneralPaperCircleFiniteAverage GeneralPaperCircleCoordinatePayoff
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable def reconstructed {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (weights : Fin g → ℕ) (values y : Fin g → ℝ) (x : Fin R → ℝ) : ℝ :=
  average (fun s:Fin (R*W) => ∑ j,values j*share (y j) (GeneralPaperCircleHardBudget.bid R W hR hW weights x s.val j))

noncomputable def comparison {g : ℕ} (R W : ℕ) (weights : Fin g → ℕ) (values y : Fin g → ℝ) (x : Fin R → ℝ) : ℝ :=
  ∑ j,values j*average (fun a => share (y j) (coefficient R W (weights j)*x a))

noncomputable def loss {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (values : Fin g → ℝ) : ℝ :=
  ∑ j,values j*((weights j:ℝ)/W)

theorem normalized_weight_loss {g : ℕ} (W Q : ℕ) (hW : 0<W) (hQ : 0<Q) (weights : Fin g → ℕ) :
    loss W weights (fun j => (weights j:ℝ)/Q)=
      (∑ j,((weights j:ℝ)/Q)^2)/((W:ℝ)/Q) := by
  have hw : (W:ℝ)≠0 := by exact_mod_cast hW.ne'
  have hq : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  unfold loss
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

theorem difference {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (values y : Fin g → ℝ) (x : Fin R → ℝ) :
    reconstructed R W hR hW weights values y x-comparison R W weights values y x=
      ∑ j,values j*(average (fun s:Fin (R*W) => share (y j) (GeneralPaperCircleHardBudget.bid R W hR hW weights x s.val j))-
        average (fun a => share (y j) (coefficient R W (weights j)*x a))) := by
  unfold reconstructed comparison
  rw [average_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [average_mul]
  ring

theorem error {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (values : Fin g → ℝ) (hv : ∀ j,0≤values j) (y : Fin g → ℝ) (x : Fin R → ℝ) (hx : Monotone x) :
    0≤reconstructed R W hR hW weights values y x-comparison R W weights values y x ∧
      reconstructed R W hR hW weights values y x-comparison R W weights values y x≤loss W weights values := by
  rw [difference]
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hv j) (bid_error R W hR hW weights x hx (y j) j).1)
  · exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (bid_error R W hR hW weights x hx (y j) j).2 (hv j))

theorem loss_le_max {g : ℕ} (W : ℕ) (hW : 0<W) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (values : Fin g → ℝ) (δ : ℝ) (hδ : ∀ j,values j≤δ) : loss W weights values≤δ := by
  have hs' : (∑ j,(weights j:ℝ))=(W:ℝ) := by exact_mod_cast hs
  unfold loss
  calc
    _ ≤ ∑ j,δ*((weights j:ℝ)/W) := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hδ j) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    _ = δ := by
      rw [←Finset.mul_sum,←Finset.sum_div,hs',div_self (by exact_mod_cast hW.ne'),mul_one]

theorem error_le_max {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (values : Fin g → ℝ) (hv : ∀ j,0≤values j) (δ : ℝ) (hδ : ∀ j,values j≤δ)
    (y : Fin g → ℝ) (x : Fin R → ℝ) (hx : Monotone x) :
    0≤reconstructed R W hR hW weights values y x-comparison R W weights values y x ∧
      reconstructed R W hR hW weights values y x-comparison R W weights values y x≤δ := by
  have h := error R W hR hW weights values hv y x hx
  exact ⟨h.1,h.2.trans (loss_le_max W hW weights hs values δ hδ)⟩

theorem mixture_error {T g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (values : Fin g → ℝ) (hv : ∀ j,0≤values j) (y : Fin g → ℝ)
    (rows : Fin T → Fin R → ℝ) (hRows : ∀ r,Monotone (rows r))
    (p : Fin T → ℝ) (hp : ∀ r,0≤p r) (hs : ∑ r,p r=1) :
    0≤(∑ r,p r*reconstructed R W hR hW weights values y (rows r))-
        (∑ r,p r*comparison R W weights values y (rows r)) ∧
      (∑ r,p r*reconstructed R W hR hW weights values y (rows r))-
        (∑ r,p r*comparison R W weights values y (rows r))≤loss W weights values := by
  have hl := Finset.sum_nonneg (s:=Finset.univ) (fun r _ =>
    mul_nonneg (hp r) (error R W hR hW weights values hv y (rows r) (hRows r)).1)
  have hu := Finset.sum_le_sum (s:=Finset.univ) (fun r _ =>
    mul_le_mul_of_nonneg_left (error R W hR hW weights values hv y (rows r) (hRows r)).2 (hp r))
  simp_rw [mul_sub,Finset.sum_sub_distrib] at hl hu
  rw [←Finset.sum_mul,hs,one_mul] at hu
  exact ⟨hl,hu⟩

end Blotto.GeneralPaperCircleLightPayoff
