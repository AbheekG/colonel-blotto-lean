import Blotto.PlayerSpecificCancellationTraceCost

/-! Actual inverse-leading normalization, retaining the computed inverse for
the later quotient rescaling. Numerical outputs refine the original code. -/
namespace Blotto.PlayerSpecificMonicizeExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run (q : Data) : (ℚ×Data)×Trace :=
  let inverted := PlayerSpecificLeadingExecution.inverseLead q
  let scaled := PlayerSpecificDenseExecution.scale inverted.1 q
  let normalized := PlayerSpecificDenseExecution.trim scaled.1
  ((inverted.1,normalized.1),inverted.2++scaled.2++normalized.2++[.control q.length])

theorem value (q : Data) : (run q).1=
    (PlayerSpecificPolynomialDivision.inverseLead q,PlayerSpecificPolynomialDivision.monicize q) := by
  simp only [run,PlayerSpecificLeadingExecution.inverseLead_value,PlayerSpecificDenseExecution.scale_value,
    PlayerSpecificDenseExecution.trim_value,PlayerSpecificPolynomialDivision.monicize]

theorem inverse_value (q : Data) : (run q).1.1=PlayerSpecificPolynomialDivision.inverseLead q := congrArg Prod.fst (value q)
theorem polynomial_value (q : Data) : (run q).1.2=PlayerSpecificPolynomialDivision.monicize q := congrArg Prod.snd (value q)

theorem inverse_height (q : Data) (H : ℕ) (hq : HasHeight q H) (hH : 1≤H) : RationalHeight (run q).1.1 H := by
  rw [inverse_value]
  exact (default_height hq hH).inv

theorem polynomial_height (q : Data) (H : ℕ) (hq : HasHeight q H) (hH : 1≤H) : HasHeight (run q).1.2 (2*H) := by
  rw [polynomial_value]
  exact PlayerSpecificDivisionHeights.monicize_height q H hq hH

theorem polynomial_length (q : Data) : (run q).1.2.length≤q.length := by
  rw [polynomial_value]
  exact PlayerSpecificDivisionHeights.monicize_length q

theorem normalized (q : Data) : Normalized (run q).1.2 := by
  rw [polynomial_value]
  exact trim_normalized _

theorem monic (q : Data) (hq : Normalized q) (hne : q≠[]) : (semantics (run q).1.2).Monic := by
  rw [polynomial_value]
  exact PlayerSpecificPolynomialDivision.monicize_monic q hq hne

def width (H : ℕ) : ℕ := 256*(H+1)

theorem cost (model : RationalCostModel) (q : Data) (H : ℕ) (hq : HasHeight q H) (hH : 1≤H) (hlen : q.length≤4) :
    price model (run q).2≤1000000*model.rat (width H) := by
  let inverted := PlayerSpecificLeadingExecution.inverseLead q
  let scaled := PlayerSpecificDenseExecution.scale inverted.1 q
  let normalized := PlayerSpecificDenseExecution.trim scaled.1
  have hiH : RationalHeight inverted.1 H := PlayerSpecificLeadingExecution.inverseLead_height q H hq hH
  have hsH : HasHeight scaled.1 (2*H) := by
    dsimp only [scaled]
    rw [PlayerSpecificDenseExecution.scale_value]
    simpa only [two_mul] using scale_height hiH hq
  have hslen : scaled.1.length≤4 := by
    dsimp only [scaled]
    rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
    exact hlen
  have hbasei := PlayerSpecificLeadingExecution.inverseLead_cost model q H 4 hq hH hlen
  have hip : price model inverted.2≤69*model.rat (width H) :=
    hbasei.trans (Nat.mul_le_mul_left 69 (model.monotone (by unfold PlayerSpecificLeadingExecution.width width; omega)))
  have hbases := PlayerSpecificDenseOperationCost.scale_cost model inverted.1 q H 4 hiH hq hlen
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hbases
  have hsp : price model scaled.2≤375000*model.rat (width H) :=
    hbases.trans (Nat.mul_le_mul_left 375000 (model.monotone (by unfold width; omega)))
  have hbasen := PlayerSpecificDenseOperationCost.trim_cost model scaled.1 (2*H) 4 hsH hslen
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hbasen
  have hnp : price model normalized.2≤375000*model.rat (width H) :=
    hbasen.trans (Nat.mul_le_mul_left 375000 (model.monotone (by unfold width; omega)))
  have hfit : Fits (width H) [.control q.length] := by
    intro e he
    have he' := List.mem_singleton.mp he
    subst e
    exact (control_width q.length).trans (by unfold width; omega)
  have hc := price_bound model (width H) (by unfold width; omega) _ hfit
  simp only [List.length_cons,List.length_nil] at hc
  change price model (inverted.2++scaled.2++normalized.2++[.control q.length])≤_
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificMonicizeExecution
