import Blotto.RationalExpressionHeight

/-! The local bit-height certificate covers every arithmetic intermediate
and comparison operand, including both statically available branches. -/

namespace Blotto.RationalExpression

def AllRunHeights {k : ℕ} (env : FixedArrayTable k ℚ) (s : ℕ) : RationalExpression k → Prop
  | .input j => RationalHeight (env.read j) s
  | .literal q => RationalHeight q s
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b =>
    RationalHeight ((a.run env).1) s ∧ RationalHeight ((b.run env).1) s ∧ a.AllRunHeights env s ∧ b.AllRunHeights env s
  | .ifLe a b yes no =>
    RationalHeight ((a.run env).1) s ∧ RationalHeight ((b.run env).1) s ∧
      a.AllRunHeights env s ∧ b.AllRunHeights env s ∧ yes.AllRunHeights env s ∧ no.AllRunHeights env s

theorem AllRunHeights_mono {k s t : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℚ) (hst : s ≤ t)
    (h : e.AllRunHeights env s) : e.AllRunHeights env t := by
  induction e with
  | input j => exact h.mono hst
  | literal q => exact h.mono hst
  | add a b ha hb => exact ⟨h.1.mono hst, h.2.1.mono hst, ha h.2.2.1, hb h.2.2.2⟩
  | sub a b ha hb => exact ⟨h.1.mono hst, h.2.1.mono hst, ha h.2.2.1, hb h.2.2.2⟩
  | mul a b ha hb => exact ⟨h.1.mono hst, h.2.1.mono hst, ha h.2.2.1, hb h.2.2.2⟩
  | div a b ha hb => exact ⟨h.1.mono hst, h.2.1.mono hst, ha h.2.2.1, hb h.2.2.2⟩
  | minimum a b ha hb => exact ⟨h.1.mono hst, h.2.1.mono hst, ha h.2.2.1, hb h.2.2.2⟩
  | maximum a b ha hb => exact ⟨h.1.mono hst, h.2.1.mono hst, ha h.2.2.1, hb h.2.2.2⟩
  | ifLe a b yes no ha hb hy hn =>
    exact ⟨h.1.mono hst, h.2.1.mono hst, ha h.2.2.1, hb h.2.2.2.1, hy h.2.2.2.2.1, hn h.2.2.2.2.2⟩

theorem run_all_heights {k : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℚ) (s : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : e.LiteralHeights s) :
    e.AllRunHeights env (expressionHeightBudget s e.depth) := by
  induction e with
  | input j => simpa only [AllRunHeights, depth, expressionHeightBudget_zero] using hEnv j
  | literal q => simpa only [AllRunHeights, LiteralHeights, depth, expressionHeightBudget_zero] using hLit
  | add a b ha hb =>
    have hDa : a.depth ≤ max a.depth b.depth + 1 := by omega
    have hDb : b.depth ≤ max a.depth b.depth + 1 := by omega
    have hma := expressionHeightBudget_mono s hDa
    have hmb := expressionHeightBudget_mono s hDb
    exact ⟨(a.run_height env s hEnv hLit.1).mono hma, (b.run_height env s hEnv hLit.2).mono hmb,
      AllRunHeights_mono a env hma (ha hLit.1), AllRunHeights_mono b env hmb (hb hLit.2)⟩
  | sub a b ha hb =>
    have hDa : a.depth ≤ max a.depth b.depth + 1 := by omega
    have hDb : b.depth ≤ max a.depth b.depth + 1 := by omega
    have hma := expressionHeightBudget_mono s hDa
    have hmb := expressionHeightBudget_mono s hDb
    exact ⟨(a.run_height env s hEnv hLit.1).mono hma, (b.run_height env s hEnv hLit.2).mono hmb,
      AllRunHeights_mono a env hma (ha hLit.1), AllRunHeights_mono b env hmb (hb hLit.2)⟩
  | mul a b ha hb =>
    have hDa : a.depth ≤ max a.depth b.depth + 1 := by omega
    have hDb : b.depth ≤ max a.depth b.depth + 1 := by omega
    have hma := expressionHeightBudget_mono s hDa
    have hmb := expressionHeightBudget_mono s hDb
    exact ⟨(a.run_height env s hEnv hLit.1).mono hma, (b.run_height env s hEnv hLit.2).mono hmb,
      AllRunHeights_mono a env hma (ha hLit.1), AllRunHeights_mono b env hmb (hb hLit.2)⟩
  | div a b ha hb =>
    have hDa : a.depth ≤ max a.depth b.depth + 1 := by omega
    have hDb : b.depth ≤ max a.depth b.depth + 1 := by omega
    have hma := expressionHeightBudget_mono s hDa
    have hmb := expressionHeightBudget_mono s hDb
    exact ⟨(a.run_height env s hEnv hLit.1).mono hma, (b.run_height env s hEnv hLit.2).mono hmb,
      AllRunHeights_mono a env hma (ha hLit.1), AllRunHeights_mono b env hmb (hb hLit.2)⟩
  | minimum a b ha hb =>
    have hDa : a.depth ≤ max a.depth b.depth + 1 := by omega
    have hDb : b.depth ≤ max a.depth b.depth + 1 := by omega
    have hma := expressionHeightBudget_mono s hDa
    have hmb := expressionHeightBudget_mono s hDb
    exact ⟨(a.run_height env s hEnv hLit.1).mono hma, (b.run_height env s hEnv hLit.2).mono hmb,
      AllRunHeights_mono a env hma (ha hLit.1), AllRunHeights_mono b env hmb (hb hLit.2)⟩
  | maximum a b ha hb =>
    have hDa : a.depth ≤ max a.depth b.depth + 1 := by omega
    have hDb : b.depth ≤ max a.depth b.depth + 1 := by omega
    have hma := expressionHeightBudget_mono s hDa
    have hmb := expressionHeightBudget_mono s hDb
    exact ⟨(a.run_height env s hEnv hLit.1).mono hma, (b.run_height env s hEnv hLit.2).mono hmb,
      AllRunHeights_mono a env hma (ha hLit.1), AllRunHeights_mono b env hmb (hb hLit.2)⟩
  | ifLe a b yes no ha hb hy hn =>
    let d := max (max a.depth b.depth) (max yes.depth no.depth) + 1
    have hDa : a.depth ≤ d := by dsimp [d]; omega
    have hDb : b.depth ≤ d := by dsimp [d]; omega
    have hDy : yes.depth ≤ d := by dsimp [d]; omega
    have hDn : no.depth ≤ d := by dsimp [d]; omega
    have hma := expressionHeightBudget_mono s hDa
    have hmb := expressionHeightBudget_mono s hDb
    have hmy := expressionHeightBudget_mono s hDy
    have hmn := expressionHeightBudget_mono s hDn
    exact ⟨(a.run_height env s hEnv hLit.1).mono hma, (b.run_height env s hEnv hLit.2.1).mono hmb,
      AllRunHeights_mono a env hma (ha hLit.1), AllRunHeights_mono b env hmb (hb hLit.2.1),
      AllRunHeights_mono yes env hmy (hy hLit.2.2.1), AllRunHeights_mono no env hmn (hn hLit.2.2.2)⟩

end Blotto.RationalExpression
