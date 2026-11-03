import Blotto.PlayerSpecificDescriptorShiftExecution

/-! Complete shift source work is an explicit polynomial in original
row height and slot count; the output height is derived, not supplied. -/
namespace Blotto.PlayerSpecificDescriptorShiftSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H slots : ℕ) : ℕ :=
  2*slots*PlayerSpecificDescriptorShiftRowSourceCost.coefficient*(H+18)^3+
    PlayerSpecificDescriptorCopySourceCost.coefficient*(H+slots+5)^5+
    PlayerSpecificDescriptorCopySourceCost.coefficient*(step H+slots+5)^5+6

theorem profile (s C X F G : ℕ) : s*(C*X)+s*(C*X)+F+G+6=2*s*C*X+F+G+6 := by ring

theorem cost {slots : ℕ} (root : Candidate) (s : Data) (d : Descriptor 3 slots) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hs : Reduced root.polynomial s ∧ HasHeight s H)
    (hd : Bounds root d H) :
    (PlayerSpecificDescriptorShiftExecution.run RationalCostModel.schoolbook root s d).2≤work H slots := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificDescriptorShiftExecution.run model root s d).1
  have hfirst : (∑ slot : Fin slots,(PlayerSpecificDescriptorShiftRowExecution.run model root s (d.first.read slot)).2)≤
      slots*(PlayerSpecificDescriptorShiftRowSourceCost.coefficient*(H+18)^3) := by
    have h:=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
      PlayerSpecificDescriptorShiftRowSourceCost.cost root s (d.first.read slot) H hm hm0 hml hmH he hv hs (hd.first slot))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,model] using h
  have hsecond : (∑ slot : Fin slots,(PlayerSpecificDescriptorShiftRowExecution.run model root s (d.second.read slot)).2)≤
      slots*(PlayerSpecificDescriptorShiftRowSourceCost.coefficient*(H+18)^3) := by
    have h:=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
      PlayerSpecificDescriptorShiftRowSourceCost.cost root s (d.second.read slot) H hm hm0 hml hmH he hv hs (hd.second slot))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,model] using h
  have henv : ∀ j,Reduced root.polynomial ((PlayerSpecificDescriptorShiftExecution.environment s).read j) ∧
      HasHeight ((PlayerSpecificDescriptorShiftExecution.environment s).read j) H := by
    intro j; simpa only [PlayerSpecificDescriptorShiftExecution.environment,FixedArrayTable.read_ofFn] using hs
  have hbase : H≤step H := (Nat.le_succ _).trans (large H)
  have hout : Bounds root result (step H) := by
    change Bounds root (PlayerSpecificDescriptorShiftExecution.run model root s d).1 (step H)
    rw [PlayerSpecificDescriptorShiftExecution.value]
    exact PlayerSpecificAlgebraicDescriptorShift.bounds root s d H hm hm0 hs hd
  have hin:=PlayerSpecificDescriptorCopySourceCost.cost root (PlayerSpecificDescriptorShiftExecution.environment s) d H hmH hml he henv hd
  have houtc:=PlayerSpecificDescriptorCopySourceCost.cost root (PlayerSpecificDescriptorShiftExecution.environment s) result (step H)
    (mono hmH hbase) hml (mono he hbase) (fun j => ⟨(henv j).1,mono (henv j).2 hbase⟩) hout
  rw [show H+3+slots+1+1=H+slots+5 by omega] at hin
  rw [show step H+3+slots+1+1=step H+slots+5 by omega] at houtc
  rw [PlayerSpecificDescriptorShiftExecution.price_equation]
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hfirst hsecond) hin) houtc) 6).trans_eq
    (profile _ _ _ _ _)

end Blotto.PlayerSpecificDescriptorShiftSourceCost
