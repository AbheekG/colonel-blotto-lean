import Blotto.PlayerSpecificTerminalPreparationFrameCost

/-! Complete source work of terminal preparation, with all endpoint,
equality, grouping and returned-frame phases joined on the same execution. -/
namespace Blotto.PlayerSpecificTerminalPreparationSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificAlgebraicEqualityCost.coefficient+PlayerSpecificAlgebraicGroupingSourceCost.coefficient+664
def work (model : RationalCostModel) (S : ℕ) : ℕ := coefficient*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)

theorem profile (P Q N S R : ℕ) :
    100*(N+1)*R+(N+1)*(P+64)*(S+1)*R+(N+1)*(Q*(S+1)*R)+500*(N+1)*R≤
      (N+1)*((P+Q+664)*(S+1)*R) := by
  nlinarith only [Nat.zero_le (N*S*R),Nat.zero_le (S*R),Nat.zero_le R]

theorem cost {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (B : ℚ) (T S : ℕ) (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hml : p.parameters.root.polynomial.length≤4) (hmS : HasHeight p.parameters.root.polynomial S)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] S)
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (hN : N+1≤S)
    (hl : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧ HasHeight (p.rows.read j).length T)
    (hs : ∀ j,Reduced p.parameters.root.polynomial (s.data.read j) ∧ HasHeight (s.data.read j) S)
    (ha : s.active.length≤N) (hpotential : (N+1)*(T+1)≤S) :
    (PlayerSpecificTerminalPreparationExecution.run model p s B).2≤(N+1)*work model S := by
  let cached:=PlayerSpecificTerminalPreparationExecution.lengths model p
  let items:=PlayerSpecificUniformItemsExecution.run model p s (List.finRange N)
  let result:=(PlayerSpecificTerminalPreparationExecution.run model p s B).1
  have hTS : T≤S := by nlinarith only [hpotential,Nat.zero_le (N*(T+1))]
  have hlS : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧ HasHeight (p.rows.read j).length S :=
    fun j => ⟨(hl j).1,mono (hl j).2 hTS⟩
  have hcached : ∀ j,Reduced p.parameters.root.polynomial (cached.1.read j) ∧ HasHeight (cached.1.read j) T := by
    intro j
    change Reduced p.parameters.root.polynomial ((FixedArrayTable.ofFn (fun k => (p.rows.read k).length)).read j) ∧
      HasHeight ((FixedArrayTable.ofFn (fun k => (p.rows.read k).length)).read j) T
    rw [FixedArrayTable.read_ofFn]
    exact hl j
  have hitems : items.1.length≤N := by simpa only [List.length_finRange] using PlayerSpecificUniformItemsExecution.length model p s (List.finRange N)
  have hpot : (items.1.length+1)*(T+1)≤S :=
    (Nat.mul_le_mul_right (T+1) (Nat.add_le_add_right hitems 1)).trans hpotential
  have hcache:=PlayerSpecificTerminalPreparationFrameCost.lengths model p S
    (fun j => ⟨(hlS j).2,by have h:=(hl j).1.2; omega⟩) hN
  have hfilter:=PlayerSpecificUniformItemsCost.cost model p s S (by omega) (by omega) hm hm0 hml hmS hlS hs
    (List.finRange N) (by simpa only [List.length_finRange] using Nat.le_of_lt hN)
  have hgroups:=PlayerSpecificAlgebraicGroupingEntryCost.cost model p.parameters.root cached.1 B items.1 T S hm hm0 hml hmS he hv hN hcached hitems hpot
  have hgroups':=hgroups.trans (Nat.mul_le_mul_right (PlayerSpecificAlgebraicGroupingSourceCost.work model S) (Nat.add_le_add_right hitems 1))
  have hgroupSizes:=PlayerSpecificAlgebraicGroupingHeights.run model p.parameters.root cached.1 B items.1 T S hm hm0 hcached hpot
  have hpartition:=PlayerSpecificTerminalPreparationExecution.groups_partition model p s B
  have hframe:=PlayerSpecificTerminalPreparationFrameCost.frame model p s B result S hmS hml he
    (fun j => ⟨(hs j).2,by have h:=(hs j).1.2; omega⟩)
    (by intro g hg; exact ⟨(hgroupSizes g hg).2,by have h:=(hgroupSizes g hg).1.2; omega⟩) ha hpartition.2
    (by dsimp only [result]; rw [hpartition.1]
        have hh:=PlayerSpecificUniformItemsExecution.length model p s (List.finRange N)
        rw [PlayerSpecificUniformItemsExecution.uniform_items,List.length_finRange] at hh
        exact hh) hN
  have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcache hfilter) hgroups') hframe
  simp only [List.length_finRange] at hsum
  exact hsum.trans (profile PlayerSpecificAlgebraicEqualityCost.coefficient PlayerSpecificAlgebraicGroupingSourceCost.coefficient N S _)

def polynomialCoefficient : ℕ := coefficient*(PlayerSpecificAlgebraicComparisonCost.widthCoefficient^2+
  PlayerSpecificAlgebraicComparisonCost.widthCoefficient)

theorem work_polynomial (S : ℕ) : work RationalCostModel.schoolbook S≤polynomialCoefficient*(S+1)^3 := by
  unfold work
  rw [PlayerSpecificAlgebraicComparisonCost.width_linear]
  exact PlayerSpecificAlgebraicPairCost.cubic_profile coefficient PlayerSpecificAlgebraicComparisonCost.widthCoefficient (S+1) (by omega)

end Blotto.PlayerSpecificTerminalPreparationSourceCost
