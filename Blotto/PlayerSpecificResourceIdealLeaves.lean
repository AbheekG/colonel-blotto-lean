import Blotto.PlayerSpecificResourceDiscrepancy

/-! Only reached leaves of the actual request/update recursion matter.
Arbitrary explicit Boolean paths certify these leaves without constructing
an execution tree or sampling unreachable branches at runtime. -/
namespace Blotto.PlayerSpecificResourceIdealLeaves
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def ForLeaves {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) : ℕ → State N → Prop
  | 0,s => P s
  | C+1,s => match request model p s with
      | none => P s
      | some frame => ForLeaves model p P C (advance model p s frame true) ∧
          ForLeaves model p P C (advance model p s frame false)

theorem of_paths {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) (C : ℕ) (s : State N)
    (h : ∀ choices,P (PlayerSpecificAlgebraicResourceLoop.run model p C s choices).1) : ForLeaves model p P C s := by
  induction C generalizing s with
  | zero => exact h []
  | succ C ih =>
    cases he : request model p s with
    | none =>
      simpa only [ForLeaves,he,PlayerSpecificAlgebraicResourceLoop.run] using h []
    | some frame =>
      rw [ForLeaves,he]
      constructor
      · apply ih
        intro choices
        simpa only [PlayerSpecificAlgebraicResourceLoop.run,he,List.headD_cons,List.tail_cons] using h (true::choices)
      · apply ih
        intro choices
        simpa only [PlayerSpecificAlgebraicResourceLoop.run,he,List.headD_cons,List.tail_cons] using h (false::choices)

theorem mono {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P Q : State N → Prop) (C : ℕ) (s : State N) (h : ForLeaves model p P C s) (hf : ∀ t,P t → Q t) :
    ForLeaves model p Q C s := by
  induction C generalizing s with
  | zero => exact hf s h
  | succ C ih =>
    cases he : request model p s with
    | none =>
      rw [ForLeaves,he] at h ⊢
      exact hf s h
    | some frame =>
      rw [ForLeaves,he] at h ⊢
      exact ⟨ih _ h.1,ih _ h.2⟩

theorem mean_error {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (f g : State N → ℝ) (E : ℝ) (C : ℕ) (s : State N)
    (hn : PlayerSpecificResourceIdealMean.Normalized model p x C s)
    (he : ForLeaves model p (fun t => |f t-g t| ≤ E) C s) :
    |PlayerSpecificResourceIdealMean.mean model p x f C s-PlayerSpecificResourceIdealMean.mean model p x g C s| ≤ E := by
  induction C generalizing s with
  | zero => exact he
  | succ C ih =>
    cases hr : request model p s with
    | none => simpa only [ForLeaves,PlayerSpecificResourceIdealMean.mean,hr] using he
    | some frame =>
      have hp := hn frame hr
      rw [ForLeaves,hr] at he
      have hU := abs_le.mp (ih _ hp.2.1 he.1)
      have hL := abs_le.mp (ih _ hp.2.2 he.2)
      have hq : 0 ≤ 1-realEvaluate frame.pair.probability x := sub_nonneg.mpr hp.1.2
      simp only [PlayerSpecificResourceIdealMean.mean,hr]
      apply abs_le.mpr
      constructor
      · have hu := mul_le_mul_of_nonneg_left hU.1 hp.1.1
        have hl := mul_le_mul_of_nonneg_left hL.1 hq
        nlinarith only [hu,hl]
      · have hu := mul_le_mul_of_nonneg_left hU.2 hp.1.1
        have hl := mul_le_mul_of_nonneg_left hL.2 hq
        nlinarith only [hu,hl]

end Blotto.PlayerSpecificResourceIdealLeaves
