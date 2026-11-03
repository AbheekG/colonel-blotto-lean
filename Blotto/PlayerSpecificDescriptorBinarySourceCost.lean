import Blotto.PlayerSpecificDescriptorBinaryExecution

/-! The complete binary table source bound is an explicit polynomial
in original row height and dimensions. All output sizes are derived. -/
namespace Blotto.PlayerSpecificDescriptorBinarySourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H N k m : ℕ) : ℕ := PlayerSpecificMixtureScalarSourceCost.complementCoefficient*(H+13)^3+
  k*(PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(H+14)^3)+
  m*(PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 2 H+14)^3)+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(H+N+k+2)^5+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(H+N+m+2)^5+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(iterate 3 H+N+(k+m)+2)^5+6

theorem cost {N k m : ℕ} (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H)
    (hp : Reduced root.polynomial p ∧ HasHeight p H) (hl : Bounds root l H) (hr : Bounds root r H) :
    (PlayerSpecificDescriptorBinaryExecution.run RationalCostModel.schoolbook root p l r).2≤work H N k m := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificDescriptorBinaryExecution.run model root p l r).1
  let comp:=(PlayerSpecificMixtureScalarExecution.complement model root p).1
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 2 H
  have hbase3:=PlayerSpecificAlgebraicExpressionBudget.initial_le 3 H
  have hcomp:=PlayerSpecificMixtureScalarSourceCost.complement_bounds model root p H hm hm0 hml hmH hH hp
  have hc:=PlayerSpecificMixtureScalarSourceCost.complement_cost root p H hm hm0 hml hmH he hv hH hp
  have hleft : (∑ slot : Fin k,(PlayerSpecificMixtureScalarExecution.scale model root p (l.weights.read slot)).2)≤
      k*(PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(H+14)^3) := by
    have h:=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
      PlayerSpecificMixtureScalarSourceCost.scale_cost root p (l.weights.read slot) H hm hm0 hml hmH he hv hp (hl.weights slot))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,model] using h
  have hright : (∑ slot : Fin m,(PlayerSpecificMixtureScalarExecution.scale model root comp (r.weights.read slot)).2)≤
      m*(PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 2 H+14)^3) := by
    have h:=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
      PlayerSpecificMixtureScalarSourceCost.scale_cost root comp (r.weights.read slot) (iterate 2 H) hm hm0 hml
        (mono hmH hbase) (mono he hbase) hv hcomp ⟨(hr.weights slot).1,mono (hr.weights slot).2 hbase⟩)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h
  have henv : ∀ j,Reduced root.polynomial ((PlayerSpecificMixtureScalarExecution.oneEnvironment p).read j) ∧
      HasHeight ((PlayerSpecificMixtureScalarExecution.oneEnvironment p).read j) H := by
    intro j; simpa only [PlayerSpecificMixtureScalarExecution.oneEnvironment,FixedArrayTable.read_ofFn] using hp
  have hfl:=PlayerSpecificDescriptorCopySourceCost.cost root (PlayerSpecificMixtureScalarExecution.oneEnvironment p) l H hmH hml he henv hl
  have hfr:=PlayerSpecificDescriptorCopySourceCost.cost root (PlayerSpecificMixtureScalarExecution.oneEnvironment p) r H hmH hml he henv hr
  have hout : Bounds root result (iterate 3 H) := by
    change Bounds root (PlayerSpecificDescriptorBinaryExecution.run model root p l r).1 (iterate 3 H)
    rw [PlayerSpecificDescriptorBinaryExecution.value]
    exact PlayerSpecificAlgebraicDescriptorBinarySizes.bounds root p l r H hm hm0 hml hmH hH hp hl hr
  have hfo:=PlayerSpecificDescriptorCopySourceCost.cost root (PlayerSpecificMixtureScalarExecution.oneEnvironment p) result (iterate 3 H)
    (mono hmH hbase3) hml (mono he hbase3) (fun j => ⟨(henv j).1,mono (henv j).2 hbase3⟩) hout
  rw [show H+N+k+1+1=H+N+k+2 by omega] at hfl
  rw [show H+N+m+1+1=H+N+m+2 by omega] at hfr
  rw [show iterate 3 H+N+(k+m)+1+1=iterate 3 H+N+(k+m)+2 by omega] at hfo
  rw [PlayerSpecificDescriptorBinaryExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc hleft) hright) hfl) hfr) hfo) 6

end Blotto.PlayerSpecificDescriptorBinarySourceCost
