import Blotto.PlayerSpecificSignedLineage

/-! Signed, nonrepeating lineages in the actual initial data have one
polynomial original-input height bound. The full coupling must maintain
these lineage certificates; that loop invariant is a separate obligation. -/
namespace Blotto.PlayerSpecificInitialLineageBound
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicInitialVector
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 2*PlayerSpecificInitialPositivePrecision.initialCoefficient+5
def height (N L : ℕ) : ℕ := coefficient*(N+1)^2*(L+1)
def means {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (firstPlayer : Bool) (j : Fin N) : Data :=
  if firstPlayer then (p.rows.read j).initialA else (p.rows.read j).initialB
def endpoints {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (j : Fin N) : Data := (p.rows.read j).length

theorem profile (K N L H : ℕ) (hH : H≤K*(N+1)*(L+1)) :
    (H+1)*(N+N)+3≤(2*K+5)*(N+1)^2*(L+1) := by
  have hS : 1≤(N+1)*(L+1) := Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤L+1)
  have hHp : H+1≤(K+1)*((N+1)*(L+1)) := by nlinarith only [hH,hS]
  have hm:=Nat.mul_le_mul hHp (show N+N≤2*(N+1) by omega)
  have hpos : 1≤(N+1)^2*(L+1) := Nat.mul_le_mul (by nlinarith : 1≤(N+1)^2) (by omega : 1≤L+1)
  nlinarith only [hm,hpos]

theorem actual_height {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (firstPlayer : Bool)
    (a : Data) (ha : Reduced r.root.polynomial a) (positive negative : List (Fin N))
    (hp : positive.Nodup) (hn : negative.Nodup)
    (hrep : PlayerSpecificSignedLineage.Represents
      (means (prepare RationalCostModel.schoolbook i r) firstPlayer) (endpoints (prepare RationalCostModel.schoolbook i r)) a positive negative) :
    HasHeight a (height N (PlayerSpecificInitialPositivePrecision.inputSize i)) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  have hred:=(reduced_rows RationalCostModel.schoolbook i r hs.1 hm0).2
  have hsize:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2
  have hv : ∀ j,Reduced r.root.polynomial (means (prepare RationalCostModel.schoolbook i r) firstPlayer j) ∧
      HasHeight (means (prepare RationalCostModel.schoolbook i r) firstPlayer j)
        (PlayerSpecificAlgebraicInitialInputSizes.height N (PlayerSpecificInitialPositivePrecision.inputSize i)) := by
    intro j
    cases firstPlayer
    · exact ⟨(hred j).2.2,(hsize j).2.2⟩
    · exact ⟨(hred j).2.1,(hsize j).2.1⟩
  have he : ∀ j,Reduced r.root.polynomial (endpoints (prepare RationalCostModel.schoolbook i r) j) ∧
      HasHeight (endpoints (prepare RationalCostModel.schoolbook i r) j)
        (PlayerSpecificAlgebraicInitialInputSizes.height N (PlayerSpecificInitialPositivePrecision.inputSize i)) :=
    fun j => ⟨(hred j).1,(hsize j).1⟩
  have h:=PlayerSpecificSignedLineage.representation_height r.root.polynomial _ _ a positive negative
    hs.1 hm0 ha _ hv he hp hn hrep
  exact mono h (profile PlayerSpecificInitialPositivePrecision.initialCoefficient N _ _
    (PlayerSpecificAlgebraicInitialInputSizes.polynomial_height N (PlayerSpecificInitialPositivePrecision.inputSize i)))

end Blotto.PlayerSpecificInitialLineageBound
