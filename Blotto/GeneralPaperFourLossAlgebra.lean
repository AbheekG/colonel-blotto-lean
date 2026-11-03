import Blotto.GeneralPaperCodeCDFDistance

/-! Exact four-loss cancellation before averaging. The loss functions are
the manuscript's finite-code derivatives, including the half-sum CDF and
one jointly normalized signed block per field. Chosen rows are retained
explicitly, so the subsequent optimizer inequality uses the same rows.
-/
namespace Blotto.GeneralPaperFourLossAlgebra
open scoped BigOperators Classical
open GeneralPaperCodeCDF GeneralPaperSignedPairing
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def pLoss {n : ℕ} (q : Fin n → ℝ) (lambda : Fin (n+n) → ℝ) (a : Fin n) : ℝ :=
  1-half q a+tail lambda a.val

noncomputable def qLoss {n : ℕ} (p : Fin n → ℝ) (mu : Fin (n+n) → ℝ) (a : Fin n) : ℝ :=
  -half p a+tail mu a.val

def multiplierLoss {n : ℕ} (p : Fin n → ℝ) (row : Fin n) (s : Fin (n+n)) : ℝ :=
  signed (fun a => rowCDF row a-cdf p a) s

def dot {α : Type*} [Fintype α] (p loss : α → ℝ) : ℝ := ∑ i, p i*loss i

noncomputable def fieldRegret {n : ℕ} (p q x y : Fin n → ℝ)
    (lambda mu testLambda testMu : Fin (n+n) → ℝ) (rowX rowY : Fin n) : ℝ :=
  dot (fun a => p a-x a) (pLoss q lambda)+dot (fun a => q a-y a) (qLoss p mu)+
    dot (fun s => lambda s-testLambda s) (multiplierLoss p rowX)+
    dot (fun s => mu s-testMu s) (multiplierLoss q rowY)

theorem p_pairing {n : ℕ} (p x q : Fin n → ℝ) (lambda : Fin (n+n) → ℝ) (hq : ∑ a, q a=1) :
    dot (fun a => p a-x a) (pLoss q lambda)=codePayoff p q-codePayoff x q+
      pair lambda (fun a => cdf p a-cdf x a) := by
  unfold dot pLoss
  simp only [mul_add,Finset.sum_add_distrib]
  rw [← payoff_defender (fun a => p a-x a) q hq,payoff_sub_left]
  rw [pair_sub_right,cdf_pair_tail,cdf_pair_tail,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem q_pairing {n : ℕ} (p q y : Fin n → ℝ) (mu : Fin (n+n) → ℝ) :
    dot (fun a => q a-y a) (qLoss p mu)=codePayoff p y-codePayoff p q+
      pair mu (fun a => cdf q a-cdf y a) := by
  unfold dot qLoss
  simp only [mul_add,Finset.sum_add_distrib]
  rw [payoff_response,payoff_response,pair_sub_right,cdf_pair_tail,cdf_pair_tail]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a ha <;> ring

theorem multiplier_pairing {n : ℕ} (p : Fin n → ℝ) (row : Fin n) (lambda test : Fin (n+n) → ℝ) :
    dot (fun s => lambda s-test s) (multiplierLoss p row)=
      pair test (fun a => cdf p a-rowCDF row a)-pair lambda (fun a => cdf p a-rowCDF row a) := by
  change pair (fun s => lambda s-test s) (fun a => rowCDF row a-cdf p a)=_
  rw [pair_sub_left,pair_sub_right,pair_sub_right,pair_sub_right,pair_sub_right]
  ring

theorem cancellation {n : ℕ} (p q x y : Fin n → ℝ)
    (lambda mu testLambda testMu : Fin (n+n) → ℝ) (rowX rowY : Fin n) (hq : ∑ a, q a=1) :
    fieldRegret p q x y lambda mu testLambda testMu rowX rowY=
      codePayoff p y-codePayoff x q+
        pair testLambda (fun a => cdf p a-rowCDF rowX a)+pair testMu (fun a => cdf q a-rowCDF rowY a)+
        (tail lambda rowX.val-pair lambda (cdf x))+(tail mu rowY.val-pair mu (cdf y)) := by
  unfold fieldRegret
  rw [p_pairing p x q lambda hq,q_pairing,multiplier_pairing,multiplier_pairing]
  simp only [pair_sub_right,pair_row]
  ring

end Blotto.GeneralPaperFourLossAlgebra
