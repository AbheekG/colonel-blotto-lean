import Blotto.PlayerSpecificThreeDrawExecution

/-! One complete source contract for every actual three-variable case,
including all preparation, finite bits, selection and interpolation. -/
namespace Blotto.PlayerSpecificThreeDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificAlgebraicThreeEnvironmentSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def drawCoefficient : ℕ := PlayerSpecificSegmentDrawSourceCost.coefficient*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^20+13)^16
def coefficient : ℕ := PlayerSpecificUnorderedThreeSourceCost.coefficient+drawCoefficient+2

theorem transfer (C B U X : ℕ) (h : U≤B*X) : C*U^16≤(C*B^16)*X^16 := by
  apply (Nat.mul_le_mul_left C (Nat.pow_le_pow_left h 16)).trans_eq
  rw [mul_pow,Nat.mul_assoc]

theorem profile (C D X : ℕ) (hX : 1≤X) : C*X+D*X+2≤(C+D+2)*X := by nlinarith only [hX]

theorem cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin (8*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificThreeDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤coefficient*(T+H+K+1)^16 := by
  let model:=RationalCostModel.schoolbook
  let prepared:=PlayerSpecificUnorderedThreeExecution.run model root a
  let U:=PlayerSpecificAlgebraicHeightEnvelope.iterate 20 T
  let A:=(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^20
  let X:=T+H+K+1
  have hX : 1≤X := by dsimp [X]; omega
  have hbase : T≤U := PlayerSpecificAlgebraicExpressionBudget.initial_le 20 T
  have hp:=PlayerSpecificUnorderedThreeSourceCost.cost root a T hm hm0 hml hmT he hv hT ha
  have hpQ : prepared.2≤PlayerSpecificUnorderedThreeSourceCost.coefficient*X^16 := hp.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (show T+1≤X by dsimp [X]; omega) 3).trans
      (Nat.pow_le_pow_right hX (by decide : 3≤16))))
  have hd : Bounds root prepared.1 U := by
    rw [PlayerSpecificUnorderedThreeExecution.value]
    exact PlayerSpecificAlgebraicThreeDescriptorSizes.unordered model root a T ha hm hm0 hml hmT hT
  have hc:=PlayerSpecificSegmentDrawSourceCost.cost root prepared.1 8 U H K bits hm hm0 hml (mono hmT hbase) (mono he hbase) hv (by omega) hd
  have hi : U+1≤A*(T+1) := PlayerSpecificAlgebraicHeightEnvelope.iterate_bound 20 T
  have hsize : U+3+9+H+K+1≤(A+13)*X := by
    dsimp only [X]
    nlinarith only [hi,Nat.zero_le (A*H),Nat.zero_le (A*K),Nat.zero_le T,Nat.zero_le H,Nat.zero_le K]
  have hcQ : (PlayerSpecificSegmentDrawExecution.run model root prepared.1 8 H K bits).2≤drawCoefficient*X^16 :=
    hc.trans (transfer _ (A+13) _ X hsize)
  have hpack : price model [.control 1]=2 := rfl
  change prepared.2+(PlayerSpecificSegmentDrawExecution.run model root prepared.1 8 H K bits).2+price model [.control 1]≤_
  rw [hpack]
  exact (Nat.add_le_add_right (Nat.add_le_add hpQ hcQ) 2).trans (profile _ _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<X) 16)))

theorem same_return_and_cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin (8*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificThreeDrawExecution.run RationalCostModel.schoolbook root a H K bits).1=PlayerSpecificAlgebraicThreeDraw.draw RationalCostModel.schoolbook root a H K bits ∧
    (PlayerSpecificThreeDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤coefficient*(T+H+K+1)^16 :=
  ⟨PlayerSpecificThreeDrawExecution.value _ root a H K bits,cost root a T H K bits hm hm0 hml hmT he hv hT ha⟩

end Blotto.PlayerSpecificThreeDrawSourceCost
