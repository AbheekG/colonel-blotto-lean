import Blotto.PlayerSpecificComplementaryDrawExecution

/-! Complete original-row source work for the complementary two-group
terminal sampler, including midpoint decoding and all returned rows. -/
namespace Blotto.PlayerSpecificComplementaryDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T K : ℕ) : ℕ :=
  (2000*(192*192+192))*(K+1)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+K+4)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step (T+K+3)+1)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*
    (PlayerSpecificAlgebraicComplementaryDraw.height T K+1)^3+
  (1200*PlayerSpecificResourceCostProfile.rationalCoefficient)*
    (PlayerSpecificAlgebraicComplementaryDraw.height T K+5)^3+2

theorem cost (root : Candidate) (budget : Data) (T K : ℕ) (bits : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ [])
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T)
    (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (_hv : root.interval.lo < root.interval.hi) (hT : 2 ≤ T)
    (hb : Reduced root.polynomial budget ∧ HasHeight budget T) :
    (PlayerSpecificComplementaryDrawExecution.run root budget K bits).2 ≤ work T K := by
  let model := RationalCostModel.schoolbook
  let G := T+K+3
  let U := step G
  let V := PlayerSpecificAlgebraicComplementaryDraw.height T K
  let F := V+4
  let midpoint := PlayerSpecificMidpointExecution.run model K bits
  let q := PlayerSpecificFieldCombinationContract.constant root.polynomial midpoint.1
  let first := PlayerSpecificAlgebraicExpressionExecution.binary model root .multiply budget q.1
  let second := PlayerSpecificAlgebraicExpressionExecution.binary model root .subtract budget first.1
  let result : FixedArrayTable 4 Data := FixedArrayTable.ofFn ![first.1,second.1,[],[]]
  have hTG : T ≤ G := by dsimp [G]; omega
  have hGU : G ≤ U := (Nat.le_succ _).trans (large G)
  have hTV : T ≤ V := hTG.trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 3 G)
  have hTF : T ≤ F := by dsimp [F]; omega
  have hVF : V ≤ F := by dsimp [F]; omega
  have hmid := PlayerSpecificMidpointCost.polynomial_cost K bits
  have hmidHeight : RationalHeight midpoint.1 G := by
    dsimp only [midpoint]
    rw [PlayerSpecificMidpointExecution.value]
    exact (dyadicMidpointSample_height K bits).mono (by dsimp [G]; omega)
  have hq := PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root midpoint.1 G
    hm hm0 hml (mono hmT hTG) hmidHeight (by dsimp [G]; omega)
  have hqReduced : Reduced root.polynomial q.1 := by
    dsimp only [q]
    rw [PlayerSpecificFieldCombinationContract.constant_value]
    exact PlayerSpecificAlgebraicField.constant_reduced root.polynomial midpoint.1 hm hm0
  have hqHeight : HasHeight q.1 U := by
    dsimp only [q,U]
    rw [PlayerSpecificFieldCombinationContract.constant_value]
    exact constant_height root.polynomial midpoint.1 G (mono hmT hTG)
      hmidHeight (by dsimp [G]; omega) hml
  have hfirst := PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .multiply
    budget q.1 U hm hm0 hml hb.1 hqReduced
    (mono hmT (hTG.trans hGU)) (mono hb.2 (hTG.trans hGU)) hqHeight
    (by
      have hG : 1 ≤ G := by
        dsimp [G]
        omega
      exact hG.trans hGU)
  have hresult : ∀ j,Reduced root.polynomial (result.read j) ∧ HasHeight (result.read j) V := by
    intro j
    change Reduced root.polynomial ((PlayerSpecificComplementaryDrawExecution.run root budget K bits).1.read j) ∧
      HasHeight ((PlayerSpecificComplementaryDrawExecution.run root budget K bits).1.read j) V
    rw [PlayerSpecificComplementaryDrawExecution.value]
    exact PlayerSpecificAlgebraicComplementaryDraw.bounds root budget T hm hm0 hml hmT hb K bits j
  have hfirstReduced : Reduced root.polynomial first.1 := by
    change Reduced root.polynomial (result.read 0)
    exact (hresult 0).1
  have hfirstHeight : HasHeight first.1 V := by
    change HasHeight (result.read 0) V
    exact (hresult 0).2
  have hsecond := PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .subtract
    budget first.1 V hm hm0 hml hb.1 hfirstReduced
    (mono hmT hTV) (mono hb.2 hTV) hfirstHeight (by omega)
  have hframe := PlayerSpecificExpressionVectorFrameCost.cost model root
    (PlayerSpecificComplementaryDrawExecution.environment budget) result F
    (mono hmT hTF) hml (mono he hTF)
    (fun j => ⟨by simpa only [PlayerSpecificComplementaryDrawExecution.environment,
        FixedArrayTable.read_ofFn] using mono hb.2 hTF,
      by have h := hb.1.2; simpa only [PlayerSpecificComplementaryDrawExecution.environment,
        FixedArrayTable.read_ofFn] using (show budget.length ≤ 3 by omega)⟩)
    (fun j => ⟨mono (hresult j).2 hVF,by have h := (hresult j).1.2; omega⟩)
    (by dsimp [F]; omega) (by dsimp [F]; omega) (by dsimp [F]; omega)
  have hq' := hq.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 G)
  have hfirst' := hfirst.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 U)
  have hsecond' := hsecond.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 V)
  have hframe' := hframe.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 1200 F)
  change midpoint.2+price model q.2+first.2+second.2+
    price model (PlayerSpecificExpressionVectorExecution.frame root
      (PlayerSpecificComplementaryDrawExecution.environment budget) result)+
    price model [.control 1] ≤ _
  rw [show price model [.control 1]=2 by rfl]
  have hsum := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hmid hq') hfirst')
      hsecond') hframe') 2
  apply hsum.trans_eq
  dsimp only [G,U,V,F]
  unfold work
  ring

theorem same_return_and_cost (root : Candidate) (budget : Data) (T K : ℕ)
    (bits : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ [])
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T)
    (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo < root.interval.hi) (hT : 2 ≤ T)
    (hb : Reduced root.polynomial budget ∧ HasHeight budget T) :
    (PlayerSpecificComplementaryDrawExecution.run root budget K bits).1 =
      PlayerSpecificAlgebraicComplementaryDraw.draw root budget K bits ∧
    (PlayerSpecificComplementaryDrawExecution.run root budget K bits).2 ≤ work T K :=
  ⟨PlayerSpecificComplementaryDrawExecution.value root budget K bits,
    cost root budget T K bits hm hm0 hml hmT he hv hT hb⟩

end Blotto.PlayerSpecificComplementaryDrawSourceCost
