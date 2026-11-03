import Blotto.GeneralPaperUniformRowLaw

/-! Canonical continuous-deviation security for the full finite-cell lift
of an actual uniform whole-row law. Heavy coordinates are retained, and
each cyclic deviation is fixed independently of the defender row. The
native named-index and selected-shift joins remain separate. -/
namespace Blotto.GeneralPaperCircleCanonicalLift
open GeneralPaperCircleFiniteAverage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def kept {h R : ℕ} (x : Allocation (h+R)) : Allocation h := fun j => x (Fin.castAdd R j)

def representatives {h R : ℕ} (x : Allocation (h+R)) : Allocation R := fun a => x (Fin.natAdd h a)

theorem split_row {h R : ℕ} (x : Allocation (h+R)) : Fin.addCases (kept x) (representatives x)=x := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [Fin.addCases_left,kept]
  · intro a
    simp only [Fin.addCases_right,representatives]

noncomputable def row {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (weights : Fin g → ℕ) (x : Allocation (h+R)) (shift : ℕ) : Allocation (h+g) :=
  GeneralPaperCircleHardBudget.reconstruct R W hR hW weights (kept x)
    (GeneralPaperCircleSortedComparison.sorted (representatives x)) shift

noncomputable def law {h g T : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (hT : 0<T)
    (weights : Fin g → ℕ) (rows : Fin T → Allocation (h+R)) : Mixed (h+g) :=
  GeneralPaperUniformRowLaw.mixture hT (fun r => GeneralPaperUniformRowLaw.law (Nat.mul_pos hR hW)
    (fun s:Fin (R*W) => row R W hR hW weights (rows r) s.val))

theorem average_const {N : ℕ} (hN : 0<N) (c : ℝ) : average (fun _:Fin N => c)=c := by
  unfold average
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (by exact_mod_cast hN.ne')

theorem average_swap {N M : ℕ} (f : Fin N → Fin M → ℝ) :
    average (fun i => average (f i))=average (fun j => average (fun i => f i j)) := by
  unfold average
  simp_rw [←Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem row_feasible {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (x : Allocation (h+R)) (B : ℝ)
    (hx : Feasible B x) (shift : ℕ) : Feasible B (row R W hR hW weights x shift) := by
  apply GeneralPaperCircleSortedComparison.reconstruct_feasible R W hR hW weights hs
  simpa only [split_row] using hx

theorem law_supported {h g T : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (hT : 0<T)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (rows : Fin T → Allocation (h+R)) (B : ℝ)
    (hx : ∀ r,Feasible B (rows r)) : Supported B (law R W hR hW hT weights rows) := by
  apply GeneralPaperUniformRowLaw.mixture_supported
  intro r
  apply GeneralPaperUniformRowLaw.law_supported
  intro s
  exact row_feasible R W hR hW weights hs (rows r) B (hx r) s.val

theorem payoff_bound {h g : ℕ} (R W Q : ℕ) (hR : 0<R) (hW : 0<W) (hQ : 0<Q)
    (weights : Fin g → ℕ) (hp : ∀ j,0<weights j) (hs : ∑ j,weights j=W)
    (v : Values (h+g)) (vRed : Values (h+R))
    (hk : ∀ j:Fin h,v.weight (Fin.castAdd g j)=vRed.weight (Fin.castAdd R j))
    (hl : ∀ j:Fin g,v.weight (Fin.natAdd h j)=(weights j:ℝ)/Q)
    (hr : ∀ a:Fin R,vRed.weight (Fin.natAdd h a)=((W:ℝ)/Q)/R)
    (yK : Allocation h) (yL : Allocation g) (hy : ∀ j,0≤yL j) (x : Allocation (h+R)) :
    average (fun s:Fin (R*W) => payoff v (Fin.addCases yK yL) (row R W hR hW weights x s.val))≤
      average (fun s:Fin R => payoff vRed (GeneralPaperCyclicQuantileDeviation.row R W hR hW weights hs yK yL s.val) x)+
      GeneralPaperCircleLightPayoff.loss W weights (fun j => (weights j:ℝ)/Q)+((W:ℝ)/Q)/R := by
  have hLift : average (fun s:Fin (R*W) => payoff v (Fin.addCases yK yL) (row R W hR hW weights x s.val))=
      (∑ j,vRed.weight (Fin.castAdd R j)*share (yK j) (kept x j))+
      GeneralPaperCircleLightPayoff.reconstructed R W hR hW weights (fun j => (weights j:ℝ)/Q) yL
        (GeneralPaperCircleSortedComparison.sorted (representatives x)) := by
    unfold payoff
    simp_rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,row,GeneralPaperCircleHardBudget.reconstruct_kept,
      GeneralPaperCircleHardBudget.reconstruct_light,hk,hl]
    rw [average_add,average_const (Nat.mul_pos hR hW)]
    rfl
  have hRed : average (fun s:Fin R => payoff vRed (GeneralPaperCyclicQuantileDeviation.row R W hR hW weights hs yK yL s.val) x)=
      (∑ j,vRed.weight (Fin.castAdd R j)*share (yK j) (kept x j))+
      average (fun s:Fin R => ∑ a,(((W:ℝ)/Q)/(R:ℝ))*share
        (GeneralPaperCyclicQuantileDeviation.representative R hR
          (GeneralPaperWeightedLowerQuantile.quantiles R W hR hW weights hs yL) s.val a) (representatives x a)) := by
    unfold payoff
    simp_rw [Fin.sum_univ_add]
    simp only [GeneralPaperCyclicQuantileDeviation.kept_read,GeneralPaperCyclicQuantileDeviation.representative_read,hr]
    rw [average_add,average_const hR]
    rfl
  rw [hLift,hRed]
  have hBound := GeneralPaperCircleQuantileComparison.reconstruction_bound R W Q hR hW hQ weights hp hs yL hy (representatives x)
  dsimp only at hBound
  linarith only [hBound]

theorem pure_bound {h g T : ℕ} (R W Q : ℕ) (hR : 0<R) (hW : 0<W) (hQ : 0<Q) (hT : 0<T)
    (weights : Fin g → ℕ) (hp : ∀ j,0<weights j) (hs : ∑ j,weights j=W)
    (v : Values (h+g)) (vRed : Values (h+R))
    (hk : ∀ j:Fin h,v.weight (Fin.castAdd g j)=vRed.weight (Fin.castAdd R j))
    (hl : ∀ j:Fin g,v.weight (Fin.natAdd h j)=(weights j:ℝ)/Q)
    (hr : ∀ a:Fin R,vRed.weight (Fin.natAdd h a)=((W:ℝ)/Q)/R)
    (rows : Fin T → Allocation (h+R)) (B : ℝ) (y : Allocation (h+g)) (hy : Feasible B y) :
    purePayoff v y (law R W hR hW hT weights rows)≤
      security vRed B (GeneralPaperUniformRowLaw.law hT rows)+
      GeneralPaperCircleLightPayoff.loss W weights (fun j => (weights j:ℝ)/Q)+((W:ℝ)/Q)/R := by
  have hYL : ∀ j,0≤representatives y j := fun j => hy.1 (Fin.natAdd h j)
  have hPoint := fun r:Fin T => payoff_bound R W Q hR hW hQ weights hp hs v vRed hk hl hr
    (kept y) (representatives y) hYL (rows r)
  simp only [split_row] at hPoint
  have hAvg := average_le _ _ hPoint
  simp_rw [average_add] at hAvg
  rw [average_const hT,average_const hT] at hAvg
  rw [average_swap (fun (r:Fin T) (s:Fin R) => payoff vRed
    (GeneralPaperCyclicQuantileDeviation.row R W hR hW weights hs (kept y) (representatives y) s.val) (rows r))] at hAvg
  have hSec : average (fun s:Fin R => average (fun r:Fin T => payoff vRed
      (GeneralPaperCyclicQuantileDeviation.row R W hR hW weights hs (kept y) (representatives y) s.val) (rows r)))≤
      security vRed B (GeneralPaperUniformRowLaw.law hT rows) := by
    rw [←average_const hR (security vRed B (GeneralPaperUniformRowLaw.law hT rows))]
    apply average_le
    intro s
    rw [←GeneralPaperUniformRowLaw.pure_law hT rows vRed]
    apply purePayoff_le_security
    apply GeneralPaperCyclicQuantileDeviation.feasible R W hR hW weights hp hs
    simpa only [split_row] using hy
  have hPure : purePayoff v y (law R W hR hW hT weights rows)=
      average (fun r:Fin T => average (fun s:Fin (R*W) => payoff v y (row R W hR hW weights (rows r) s.val))) := by
    rw [law,GeneralPaperUniformRowLaw.pure_mixture]
    simp_rw [GeneralPaperUniformRowLaw.pure_law]
  rw [hPure]
  linarith only [hAvg,hSec]

theorem security_bound {h g T : ℕ} (R W Q : ℕ) (hR : 0<R) (hW : 0<W) (hQ : 0<Q) (hT : 0<T)
    (weights : Fin g → ℕ) (hp : ∀ j,0<weights j) (hs : ∑ j,weights j=W)
    (v : Values (h+g)) (vRed : Values (h+R))
    (hk : ∀ j:Fin h,v.weight (Fin.castAdd g j)=vRed.weight (Fin.castAdd R j))
    (hl : ∀ j:Fin g,v.weight (Fin.natAdd h j)=(weights j:ℝ)/Q)
    (hr : ∀ a:Fin R,vRed.weight (Fin.natAdd h a)=((W:ℝ)/Q)/R)
    (rows : Fin T → Allocation (h+R)) (B : ℝ) (hB : 0≤B) :
    security v B (law R W hR hW hT weights rows)≤
      security vRed B (GeneralPaperUniformRowLaw.law hT rows)+
      GeneralPaperCircleLightPayoff.loss W weights (fun j => (weights j:ℝ)/Q)+((W:ℝ)/Q)/R := by
  apply security_le v hB
  intro y hy
  exact pure_bound R W Q hR hW hQ hT weights hp hs v vRed hk hl hr rows B y hy

end Blotto.GeneralPaperCircleCanonicalLift
