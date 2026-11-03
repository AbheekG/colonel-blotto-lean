import Blotto.GeneralPaperProfitRetentionFactor

/-! Convert the native grid's exact natural cross-products into rational
profit guarantees. The executable rounding functions remain unchanged.
-/
namespace Blotto.GeneralPaperProfitRationalRound
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperProfitRetentionFactor
set_option autoImplicit false
set_option maxHeartbeats 3500000

def value (q w B : ℕ) (label : Fin (prepare q w B).size) : ℚ :=
  ((prepare q w B).numerators.read label:ℚ)/(denominator w B:ℚ)

def profit (q P : ℕ) : ℚ := (P:ℚ)/(q:ℚ)

theorem value_nonnegative (q w B : ℕ) (label : Fin (prepare q w B).size) : 0≤value q w B label := by
  unfold value
  positivity

theorem profit_nonnegative (q P : ℕ) : 0≤profit q P := by unfold profit; positivity

theorem value_mono (q w B : ℕ) (i j : Fin (prepare q w B).size) (hIJ : i≤j) : value q w B i≤value q w B j := by
  unfold value
  exact div_le_div_of_nonneg_right (by exact_mod_cast (strict q w B).monotone hIJ) (by positivity)

theorem profit_add (q a b : ℕ) : profit q (a+b)=profit q a+profit q b := by unfold profit; push_cast; ring

theorem leaf_relative (q w B P : ℕ) (hQ : 0<q) (hW : 0<w) (hLow : q≤P*2^B) (hHigh : P≤2*q) :
    factor w*profit q P≤value q w B (GeneralPaperProfitGridRound.leaf (prepare q w B) P).label := by
  have hw : (0:ℚ)<w := by exact_mod_cast hW
  have hq : (0:ℚ)<q := by exact_mod_cast hQ
  have hf : (0:ℚ)<denominator w B := by exact_mod_cast denominator_positive w B hW
  have he := GeneralPaperProfitGridCover.leaf_relative q w B P hQ hW hLow hHigh
  have hc : ((w-1:ℕ):ℚ)*((P:ℚ)*(denominator w B:ℚ))≤
      (w:ℚ)*((q:ℚ)*((prepare q w B).numerators.read (GeneralPaperProfitGridRound.leaf (prepare q w B) P).label:ℚ)) := by exact_mod_cast he
  rw [factor_formula w hW]
  unfold profit value
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hw hq) hf).mpr
  nlinarith only [hc]

theorem merge_relative (q w B P : ℕ) (hW : 0<w) (hLow : w≤P) (hHigh : P≤2*denominator w B) :
    factor w*((P:ℚ)/(denominator w B:ℚ))≤value q w B (GeneralPaperProfitGridRound.merge (prepare q w B) P).label := by
  have hw : (0:ℚ)<w := by exact_mod_cast hW
  have he := GeneralPaperProfitGridCover.merge_relative q w B P hW hLow hHigh
  have hc : factor w*(P:ℚ)≤((prepare q w B).numerators.read (GeneralPaperProfitGridRound.merge (prepare q w B) P).label:ℚ) := by
    rw [factor_formula w hW,div_mul_eq_mul_div]
    apply (div_le_iff₀ hw).mpr
    have hcast : ((w-1:ℕ):ℚ)*(P:ℚ)≤(w:ℚ)*
        ((prepare q w B).numerators.read (GeneralPaperProfitGridRound.merge (prepare q w B) P).label:ℚ) := by exact_mod_cast he
    nlinarith only [hcast]
  unfold value
  calc
    _ = (factor w*(P:ℚ))/(denominator w B:ℚ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end Blotto.GeneralPaperProfitRationalRound
