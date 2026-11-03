import Blotto.PlayerSpecificAlgebraicInitialValues

/-! Actual sampler input vector from accepted finite-bit parameters. The
scale inverse is computed once and shared across original field indices;
each field caches one exact branch test and reduced marginal/mixture rows. -/
namespace Blotto.PlayerSpecificAlgebraicInitialVector
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result (N : ℕ) where
  parameters : PlayerSpecificFiniteParameterReturn.Result
  inverseScale : Data
  rows : FixedArrayTable N PlayerSpecificAlgebraicInitial.Result

def prepare {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result) : Result N :=
  let inverseScale:=PlayerSpecificAlgebraicField.inverse r.root.polynomial r.scale
  ⟨r,inverseScale,FixedArrayTable.ofFn (fun j =>
    PlayerSpecificAlgebraicInitial.run model r.root inverseScale (i.valuesA.weight j) (i.valuesB.weight j))⟩
def run {N : ℕ} (i : RationalPlayerSpecificInput N) : Option (Result N) :=
  (PlayerSpecificFiniteParameterDescription.run i).parameters.map (prepare RationalCostModel.schoolbook i)

theorem read {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result) (j : Fin N) :
    (prepare model i r).rows.read j=PlayerSpecificAlgebraicInitial.run model r.root
      (PlayerSpecificAlgebraicField.inverse r.root.polynomial r.scale) (i.valuesA.weight j) (i.valuesB.weight j) :=
  FixedArrayTable.read_ofFn _ j

theorem accepted_unique {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    ∃! x : ℝ,realEvaluate r.root.polynomial x=0 ∧ r.root.interval.Contains x := by
  have hold : PlayerSpecificFiniteParameterReturn.run RationalCostModel.schoolbook i=some r :=
    (PlayerSpecificFiniteParameterDescription.value i).symm.trans hr
  cases hchosen : PlayerSpecificFiniteRecognition.run RationalCostModel.schoolbook i with
  | none => rw [PlayerSpecificFiniteParameterReturn.run,hchosen] at hold; cases hold
  | some chosen =>
    have hs:=(PlayerSpecificFiniteRecognition.sound RationalCostModel.schoolbook i chosen.1 chosen.2 hchosen).1
    rw [PlayerSpecificFiniteParameterReturn.run,hchosen] at hold
    have he:=Option.some.inj hold
    subst r
    exact hs.2.2.2.1

theorem reduced_rows {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result) (hm : Normalized r.root.polynomial) (hm0 : r.root.polynomial≠[]) :
    Reduced r.root.polynomial (prepare model i r).inverseScale ∧
      ∀ j,Reduced r.root.polynomial ((prepare model i r).rows.read j).length ∧
        Reduced r.root.polynomial ((prepare model i r).rows.read j).initialA ∧
        Reduced r.root.polynomial ((prepare model i r).rows.read j).initialB := by
  refine ⟨PlayerSpecificAlgebraicField.inverse_reduced _ _ hm hm0,?_⟩
  intro j
  rw [read]
  exact PlayerSpecificAlgebraicInitial.reduced_result model r.root _ _ _ hm hm0

theorem values {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result) (hm : Normalized r.root.polynomial)
    (hirr : Irreducible (semantics r.root.polynomial)) (hs : Reduced r.root.polynomial r.scale)
    (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x) (hg : 0<x) :
    ∀ j,realEvaluate ((prepare model i r).rows.read j).length x=
        PlayerSpecificMarginals.length (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x (realEvaluate r.scale x) ∧
      realEvaluate ((prepare model i r).rows.read j).initialA x=
        PlayerSpecificMarginals.probA (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x*
          PlayerSpecificMarginals.length (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x (realEvaluate r.scale x) ∧
      realEvaluate ((prepare model i r).rows.read j).initialB x=
        PlayerSpecificMarginals.probB (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x*
          PlayerSpecificMarginals.length (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x (realEvaluate r.scale x) := by
  have hnode : r.root.interval.lo<r.root.interval.hi := by exact_mod_cast hx.2.1.1.trans_le hx.2.1.2
  have hinv:=PlayerSpecificAlgebraicField.inverse_value r.root.polynomial r.scale hm hirr hs x hx.1
  intro j
  rw [read]
  exact PlayerSpecificAlgebraicInitialValues.actual_values model r.root _ (i.valuesA.weight j) (i.valuesB.weight j)
    hm hirr hnode x (realEvaluate r.scale x) hx (by exact_mod_cast i.valuesA.positive j)
    (by exact_mod_cast i.valuesB.positive j) hg hinv

end Blotto.PlayerSpecificAlgebraicInitialVector
