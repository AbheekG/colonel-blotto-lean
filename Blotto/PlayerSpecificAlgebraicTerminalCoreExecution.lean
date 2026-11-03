import Blotto.PlayerSpecificAlgebraicTerminalCorePreparationSizes

/-! Reached resource data now drives the actual terminal core directly.
All core hypotheses and sizes are derived from its computed groups and
fractional quotient, without a supplied real core or branch oracle. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCoreExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalCoreDraw PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ)
    (H K : ℕ) (bits : Fin (bitCount H K) → Bool) : FixedArrayTable 4 Data :=
  let g := PlayerSpecificAlgebraicTerminalPreparation.prepare RationalCostModel.schoolbook p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  draw p.parameters a H K bits

def height (N T K : ℕ) : ℕ := PlayerSpecificAlgebraicTerminalCoreDrawBounds.height
  (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T) K

theorem every_path {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight B T) (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (H K : ℕ) (bits : Fin (bitCount H K) → Bool) :
    FullBudget (B:ℝ) (values (run p s B H K bits) x) ∧
      ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial ((run p s B H K bits).read j) ∧
        HasHeight ((run p s B H K bits).read j) (height N T K) := by
  let g := PlayerSpecificAlgebraicTerminalPreparation.prepare RationalCostModel.schoolbook p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let U := PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T
  have ha := PlayerSpecificAlgebraicTerminalCorePreparation.valid RationalCostModel.schoolbook p s B x hc hs hB hL hb hmass hend T hsize
  have hf := PlayerSpecificAlgebraicTerminalCorePreparationSizes.fits RationalCostModel.schoolbook p s B x hc hs hB hL hb hmass hend
    T hroot hml hBH hsize hresource
  have hTU : T ≤ U := by
    have h0 : T ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans (PlayerSpecificAlgebraicHeightEnvelope.large _))
  have hU : 2 ≤ U := by
    have h0 : 2 ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans (PlayerSpecificAlgebraicHeightEnvelope.large _))
  have hmU := PlayerSpecificPolynomialHeights.mono hroot hTU
  have hbudget := PlayerSpecificAlgebraicTerminalCoreDraw.every_path p.parameters a hc.normalized hc.irreducible hc.interval x hc.root
    ha U hf hml hmU hU H K bits
  have he : realEvaluate a.budget x=(B:ℝ) := PlayerSpecificAlgebraicField.constant_value _ B x hc.root.1
  rw [he] at hbudget
  exact ⟨hbudget,PlayerSpecificAlgebraicTerminalCoreDrawBounds.bounds p.parameters a hc.normalized hc.irreducible hc.interval x hc.root
    ha U hf hml hmU hU H K bits⟩

end Blotto.PlayerSpecificAlgebraicTerminalCoreExecution
