import Blotto.PlayerSpecificAlgebraicExpressionBudget

/-! Every returned local expression row has height linear in the input
height when syntax depth is fixed, and remains reduced in the same field. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicExpressionBudget
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem run_height {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (H : ℕ) (hmH : HasHeight root.polynomial H) (hH : 1≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) (hLit : e.LiteralHeights H) :
    HasHeight (PlayerSpecificAlgebraicExpression.run model root env e) (height e H) := by
  have hred:=fun e => PlayerSpecificAlgebraicExpression.reduced model root env e hm hm0 (fun j => (hEnv j).1)
  induction e with
  | input j => exact mono (hEnv j).2 (initial_le 1 H)
  | literal q => exact constant_height _ _ H hmH hLit hH hml
  | add a b ha hb =>
      let T:=iterate (max a.depth b.depth+1) H
      have haT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) T :=
        mono (ha hLit.1) (depth_mono H (le_max_left a.depth b.depth))
      have hbT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env b) T :=
        mono (hb hLit.2) (depth_mono H (le_max_right a.depth b.depth))
      have hbase : H≤T := initial_le _ H
      have hres:=binary_heights model root (PlayerSpecificAlgebraicExpression.run model root env a)
        (PlayerSpecificAlgebraicExpression.run model root env b) T hm hm0 hml (hred a) (hred b)
        (mono hmH hbase) haT hbT (hH.trans hbase)
      exact hres.1
  | sub a b ha hb =>
      let T:=iterate (max a.depth b.depth+1) H
      have haT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) T :=
        mono (ha hLit.1) (depth_mono H (le_max_left a.depth b.depth))
      have hbT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env b) T :=
        mono (hb hLit.2) (depth_mono H (le_max_right a.depth b.depth))
      have hbase : H≤T := initial_le _ H
      have hres:=binary_heights model root (PlayerSpecificAlgebraicExpression.run model root env a)
        (PlayerSpecificAlgebraicExpression.run model root env b) T hm hm0 hml (hred a) (hred b)
        (mono hmH hbase) haT hbT (hH.trans hbase)
      exact hres.2.1
  | mul a b ha hb =>
      let T:=iterate (max a.depth b.depth+1) H
      have haT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) T :=
        mono (ha hLit.1) (depth_mono H (le_max_left a.depth b.depth))
      have hbT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env b) T :=
        mono (hb hLit.2) (depth_mono H (le_max_right a.depth b.depth))
      have hbase : H≤T := initial_le _ H
      have hres:=binary_heights model root (PlayerSpecificAlgebraicExpression.run model root env a)
        (PlayerSpecificAlgebraicExpression.run model root env b) T hm hm0 hml (hred a) (hred b)
        (mono hmH hbase) haT hbT (hH.trans hbase)
      exact hres.2.2.1
  | div a b ha hb =>
      let T:=iterate (max a.depth b.depth+1) H
      have haT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) T :=
        mono (ha hLit.1) (depth_mono H (le_max_left a.depth b.depth))
      have hbT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env b) T :=
        mono (hb hLit.2) (depth_mono H (le_max_right a.depth b.depth))
      have hbase : H≤T := initial_le _ H
      have hres:=binary_heights model root (PlayerSpecificAlgebraicExpression.run model root env a)
        (PlayerSpecificAlgebraicExpression.run model root env b) T hm hm0 hml (hred a) (hred b)
        (mono hmH hbase) haT hbT (hH.trans hbase)
      exact hres.2.2.2.1
  | minimum a b ha hb =>
      let T:=iterate (max a.depth b.depth+1) H
      have haT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) T :=
        mono (ha hLit.1) (depth_mono H (le_max_left a.depth b.depth))
      have hbT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env b) T :=
        mono (hb hLit.2) (depth_mono H (le_max_right a.depth b.depth))
      have hbase : H≤T := initial_le _ H
      have hres:=binary_heights model root (PlayerSpecificAlgebraicExpression.run model root env a)
        (PlayerSpecificAlgebraicExpression.run model root env b) T hm hm0 hml (hred a) (hred b)
        (mono hmH hbase) haT hbT (hH.trans hbase)
      exact hres.2.2.2.2.1
  | maximum a b ha hb =>
      let T:=iterate (max a.depth b.depth+1) H
      have haT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) T :=
        mono (ha hLit.1) (depth_mono H (le_max_left a.depth b.depth))
      have hbT : HasHeight (PlayerSpecificAlgebraicExpression.run model root env b) T :=
        mono (hb hLit.2) (depth_mono H (le_max_right a.depth b.depth))
      have hbase : H≤T := initial_le _ H
      have hres:=binary_heights model root (PlayerSpecificAlgebraicExpression.run model root env a)
        (PlayerSpecificAlgebraicExpression.run model root env b) T hm hm0 hml (hred a) (hred b)
        (mono hmH hbase) haT hbT (hH.trans hbase)
      exact hres.2.2.2.2.2
  | ifLe a b yes no _ _ hy hn =>
      have hyes : yes.depth+1≤max (max a.depth b.depth) (max yes.depth no.depth)+1 := by omega
      have hno : no.depth+1≤max (max a.depth b.depth) (max yes.depth no.depth)+1 := by omega
      have hY:=mono (hy hLit.2.2.1) ((fuel_mono H hyes).trans
        ((Nat.le_succ _).trans (large (iterate (max (max a.depth b.depth) (max yes.depth no.depth)+1) H))))
      have hN:=mono (hn hLit.2.2.2) ((fuel_mono H hno).trans
        ((Nat.le_succ _).trans (large (iterate (max (max a.depth b.depth) (max yes.depth no.depth)+1) H))))
      simp only [PlayerSpecificAlgebraicExpression.run]
      split
      · exact hY
      · exact hN

end Blotto.PlayerSpecificAlgebraicExpressionHeights
