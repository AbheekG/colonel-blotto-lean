import Blotto.GeneralPaperOrderedProfitRetention
import Blotto.GeneralPaperProfitRationalRound

/-! Nonnegative integer input profits give the common subtree bound. This
metadata is about actual input options, not an optimizer-accuracy oracle.
The final source must derive it from the normalized battlefield values.
-/
namespace Blotto.GeneralPaperOrderedProfitTreeBounds
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperOrderedMinimum
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperProfitRationalRound
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

def BoundedProfit {K h : ℕ} (q : ℕ) (tree : Tree R K h) : Prop :=
  ∀ labels cost profit, Realizes tree labels cost profit → profit≤2*q

theorem left_bound {K h q : ℕ} (left right : Tree R K h) (hBound : BoundedProfit q (.node left right))
    (labels : List (Fin K)) (cost : R) (profit : ℕ) (hRight : Realizes right labels cost profit) : BoundedProfit q left := by
  intro ll lc lp hl
  have he := hBound (ll++labels) (lc+cost) (lp+profit) ⟨ll,lc,lp,labels,cost,profit,hl,hRight,rfl,rfl,rfl⟩
  omega

theorem right_bound {K h q : ℕ} (left right : Tree R K h) (hBound : BoundedProfit q (.node left right))
    (labels : List (Fin K)) (cost : R) (profit : ℕ) (hLeft : Realizes left labels cost profit) : BoundedProfit q right := by
  intro rr rc rp hr
  have he := hBound (labels++rr) (cost+rc) (profit+rp) ⟨labels,cost,profit,rr,rc,rp,hLeft,hr,rfl,rfl,rfl⟩
  omega

theorem cross_value_le_profit (q w B P : ℕ) (hQ : 0<q) (hW : 0<w) (label : Fin (prepare q w B).size)
    (hCross : q*(prepare q w B).numerators.read label≤P*denominator w B) : value q w B label≤profit q P := by
  have hq : (0:ℚ)<q := by exact_mod_cast hQ
  have hf : (0:ℚ)<denominator w B := by exact_mod_cast denominator_positive w B hW
  unfold value profit
  apply (div_le_div_iff₀ hf hq).mpr
  have hc : (q:ℚ)*((prepare q w B).numerators.read label:ℚ)≤(P:ℚ)*(denominator w B:ℚ) := by exact_mod_cast hCross
  nlinarith only [hc]

theorem sum_values (q w B : ℕ) (i j : Fin (prepare q w B).size) :
    (((prepare q w B).numerators.read i+(prepare q w B).numerators.read j:ℕ):ℚ)/(denominator w B:ℚ)=
      value q w B i+value q w B j := by
  unfold value
  push_cast
  ring

theorem pair_sum_bound {K h q w B : ℕ} (left right : Tree R K h) (hQ : 0<q)
    (hBound : BoundedProfit q (.node left right)) (i j : Fin (prepare q w B).size)
    (a b : Selection R (Trace K (prepare q w B).size h))
    (hl : (run (prepare q w B) left).table.read i=some a) (hr : (run (prepare q w B) right).table.read j=some b) :
    (prepare q w B).numerators.read i+(prepare q w B).numerators.read j≤2*denominator w B := by
  obtain ⟨ll,lp,_,hlr,hlp⟩ := state_sound left i a hl
  obtain ⟨rr,rp,_,hrr,hrp⟩ := state_sound right j b hr
  have hProfit := hBound (ll++rr) (a.cost+b.cost) (lp+rp) ⟨ll,a.cost,lp,rr,b.cost,rp,hlr,hrr,rfl,rfl,rfl⟩
  have hc : q*((prepare q w B).numerators.read i+(prepare q w B).numerators.read j)≤q*(2*denominator w B) := by
    have he := Nat.mul_le_mul_right (denominator w B) hProfit
    nlinarith only [hlp,hrp,he]
  exact Nat.le_of_mul_le_mul_left hc hQ

end Blotto.GeneralPaperOrderedProfitTreeBounds
