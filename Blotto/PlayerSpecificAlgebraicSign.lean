import Blotto.PlayerSpecificSignPrecision

/-! Complete computed exact sign at the retained selected real root.
The zero branch is coefficientwise. Otherwise a computed certificate gap
and refinement depth make one exact rational midpoint evaluation sufficient.
Source prices and linear refinement-endpoint heights remain separate. -/
namespace Blotto.PlayerSpecificAlgebraicSign
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificIsolationState PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 3000000

def leaf (m a : Data) (node : Interval) : Interval :=
  let prepared:=prepare m
  PlayerSpecificSelectedRefinement.run prepared (PlayerSpecificSignPrecision.depth m a node)
    (PlayerSpecificSignEnclosure.retag prepared node)
def run (m a : Data) (node : Interval) : SignType :=
  if a=[] then 0 else sign (evaluate a (leaf m a node).midpoint)

theorem perturbation (v w B : ℝ) (hB : 0<B) (hgap : 1/B≤|v|) (hclose : |v-w|<1/(4*B)) : sign w=sign v := by
  have hG : (0:ℝ)<1/B := one_div_pos.mpr hB
  have he : (1/B)/4=1/(4*B) := by field_simp
  rw [←he] at hclose
  have hd:=abs_lt.mp hclose
  by_cases hv : 0<v
  · rw [abs_of_pos hv] at hgap
    have hw : 0<w := by nlinarith only [hG,hgap,hd.2]
    rw [sign_pos hw,sign_pos hv]
  · have hn : v≤0 := le_of_not_gt hv
    rw [abs_of_nonpos hn] at hgap
    have hv' : v<0 := by nlinarith only [hG,hgap]
    have hw : w<0 := by nlinarith only [hG,hgap,hd.1]
    rw [sign_neg hw,sign_neg hv']

theorem correct (m a : Data) (node : Interval) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (ha : Reduced m a) (hv : node.lo<node.hi) (x : ℝ)
    (hu : PlayerSpecificSelectedRefinement.Unique m node x) : run m a node=sign (realEvaluate a x) := by
  by_cases hz : a=[]
  · simp only [run,hz,ite_true,realEvaluate,List.foldr_nil,sign_zero]
  · have hm0 : m≠[] := by intro he; exact hirr.ne_zero (by rw [he]; rfl)
    have ha0:=nonzero a ha.1 hz
    have hdeg:=degree_lt m a hm hm0 ha ha0
    let prepared:=prepare m
    let initial:=PlayerSpecificSignEnclosure.retag prepared node
    let L:=leaf m a node
    let M:=PlayerSpecificSignEnclosure.magnitude node
    have hi : Valid prepared initial := PlayerSpecificSignEnclosure.initial_valid prepared node hv
    have hix : PlayerSpecificSelectedRefinement.Unique m initial x := hu
    have hL : Valid prepared L := PlayerSpecificSelectedRefinement.run_valid prepared _ initial hi
    have hLx : PlayerSpecificSelectedRefinement.Unique m L x :=
      PlayerSpecificSelectedRefinement.run_unique prepared hirr.ne_zero _ initial hi x hix
    have hmiddle : L.Contains (L.midpoint:ℝ) := by
      have hb:=midpoint_between L hL.1
      constructor
      · exact_mod_cast hb.1
      · exact_mod_cast hb.2.le
    have hmiddleNode : node.Contains (L.midpoint:ℝ) :=
      PlayerSpecificSelectedRefinement.run_contained prepared _ initial hi _ hmiddle
    have hxM : |x| ≤ (M:ℝ) := PlayerSpecificSignEnclosure.inside_bound node x hu.2.1
    have hyM : |(L.midpoint:ℝ)| ≤ (M:ℝ) := PlayerSpecificSignEnclosure.inside_bound node _ hmiddleNode
    have hgap:=PlayerSpecificAlgebraicSignMagnitude.gap m a hirr ha0 hdeg M x hu.1 hxM
    have hvar:=PlayerSpecificAlgebraicSignMagnitude.variation a M x (L.midpoint:ℝ) hxM hyM
    have hdist:=PlayerSpecificIsolationBounds.contains_distance L x (L.midpoint:ℝ) hLx.2.1 hmiddle
    have hLpos : (0:ℝ)<(PlayerSpecificAlgebraicSignMagnitude.lipschitz a M:ℝ) := by
      exact_mod_cast PlayerSpecificAlgebraicSignMagnitude.lipschitz_positive a M
    have hwidth : L.width=node.width/(2:ℚ)^PlayerSpecificSignPrecision.depth m a node :=
      PlayerSpecificSelectedRefinement.run_width prepared _ initial
    have hclose : |realEvaluate a x-realEvaluate a (L.midpoint:ℝ)| <
        (1:ℝ)/(4*(PlayerSpecificAlgebraicSignMagnitude.gapDenominator m a M:ℝ)) := by
      calc
        _ ≤ (PlayerSpecificAlgebraicSignMagnitude.lipschitz a M:ℝ)*|x-(L.midpoint:ℝ)| := hvar
        _ < (PlayerSpecificAlgebraicSignMagnitude.lipschitz a M:ℝ)*(L.width:ℝ) := mul_lt_mul_of_pos_left hdist hLpos
        _ = (PlayerSpecificAlgebraicSignMagnitude.lipschitz a M:ℝ)*
            ((node.width/(2:ℚ)^PlayerSpecificSignPrecision.depth m a node:ℚ):ℝ) := by rw [hwidth]
        _ < _ := PlayerSpecificSignPrecision.sufficient_width m a node
    have hBpos : (0:ℝ)<(PlayerSpecificAlgebraicSignMagnitude.gapDenominator m a M:ℝ) := by
      exact_mod_cast PlayerSpecificAlgebraicSignMagnitude.gap_positive m a M
    have hs:=perturbation (realEvaluate a x) (realEvaluate a (L.midpoint:ℝ)) _ hBpos hgap hclose
    rw [evaluate_cast,rational_sign_cast] at hs
    simpa only [run,hz,ite_false] using hs

end Blotto.PlayerSpecificAlgebraicSign
