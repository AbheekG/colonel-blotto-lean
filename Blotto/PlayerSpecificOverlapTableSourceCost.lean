import Blotto.PlayerSpecificOverlapTableExecution

/-! Complete overlap table source work is polynomial in original row
height and both parent dimensions, with every temporary size derived. -/
namespace Blotto.PlayerSpecificOverlapTableSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def countWork (k h : ℕ) : ℕ := (64*(192^2+192))*(k+h+k*h+3)^3
def work (H k h : ℕ) : ℕ := countWork k h+(k*h)*PlayerSpecificOverlapEntrySourceCost.work H k h+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(H+k+6)^5+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(H+h+6)^5+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(iterate 10 H+k*h+7)^5+6

theorem count_cost (k h : ℕ) : (PlayerSpecificNaturalExecution.binary RationalCostModel.schoolbook (fun a b => a*b) k h).2≤countWork k h := by
  let S:=k+h+k*h+2
  let model:=RationalCostModel.schoolbook
  have hc:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a*b) k h (PlayerSpecificBitSliceCost.width S)
    (PlayerSpecificBitSliceCost.word_bound S k (by dsimp [S]; omega))
    (PlayerSpecificBitSliceCost.word_bound S h (by dsimp [S]; omega))
    (PlayerSpecificBitSliceCost.word_bound S (k*h) (by dsimp [S]; omega))
  exact hc.trans (PlayerSpecificNestedPacketSourceCost.rational 64 S)

theorem cost {k h : ℕ} (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (hf : Bounds root first H) (hs : Bounds root second H)
    (hi : Reduced root.polynomial interval ∧ HasHeight interval H) (hb : Reduced root.polynomial budget ∧ HasHeight budget H) :
    (PlayerSpecificOverlapTableExecution.run RationalCostModel.schoolbook root first second interval budget).2≤work H k h := by
  let model:=RationalCostModel.schoolbook
  let env:=PlayerSpecificOverlapTableExecution.scalars interval budget
  let result:=(PlayerSpecificOverlapTableExecution.run model root first second interval budget).1
  have henv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H := by
    intro j
    fin_cases j
    · simpa [env,PlayerSpecificOverlapTableExecution.scalars,FixedArrayTable.read_ofFn] using hi
    · simpa [env,PlayerSpecificOverlapTableExecution.scalars,FixedArrayTable.read_ofFn] using hb
  have hrows : (∑ slot : Fin (k*h),(PlayerSpecificOverlapEntryExecution.run model root first second interval budget slot).2)≤
      (k*h)*PlayerSpecificOverlapEntrySourceCost.work H k h := by
    have hc:=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
      PlayerSpecificOverlapEntrySourceCost.cost root first second interval budget slot H hm hm0 hml hmH he hv hH hf hs hi hb)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,model] using hc
  have hfirst:=PlayerSpecificDescriptorCopySourceCost.cost root env first H hmH hml he henv hf
  have hsecond:=PlayerSpecificDescriptorCopySourceCost.cost root env second H hmH hml he henv hs
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 10 H
  have hout : Bounds root result (iterate 10 H) := by
    change Bounds root (PlayerSpecificOverlapTableExecution.run model root first second interval budget).1 (iterate 10 H)
    rw [PlayerSpecificOverlapTableExecution.value]
    exact PlayerSpecificAlgebraicOverlapTable.bounds model root first second interval budget H hf hs hi hb hm hm0 hml hmH hH
  have hreturn:=PlayerSpecificDescriptorCopySourceCost.cost root env result (iterate 10 H) (mono hmH hbase) hml (mono he hbase)
    (fun j => ⟨(henv j).1,mono (henv j).2 hbase⟩) hout
  rw [show H+3+k+2+1=H+k+6 by omega] at hfirst
  rw [show H+3+h+2+1=H+h+6 by omega] at hsecond
  rw [show iterate 10 H+4+k*h+2+1=iterate 10 H+k*h+7 by omega] at hreturn
  rw [PlayerSpecificOverlapTableExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (count_cost k h) hrows) hfirst) hsecond) hreturn) 6

theorem same_return_and_cost {k h : ℕ} (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (hf : Bounds root first H) (hs : Bounds root second H)
    (hi : Reduced root.polynomial interval ∧ HasHeight interval H) (hb : Reduced root.polynomial budget ∧ HasHeight budget H) :
    (PlayerSpecificOverlapTableExecution.run RationalCostModel.schoolbook root first second interval budget).1=
      PlayerSpecificAlgebraicOverlapTable.prepare RationalCostModel.schoolbook root first second interval budget ∧
    (PlayerSpecificOverlapTableExecution.run RationalCostModel.schoolbook root first second interval budget).2≤work H k h :=
  ⟨PlayerSpecificOverlapTableExecution.value _ root first second interval budget,cost root first second interval budget H hm hm0 hml hmH he hv hH hf hs hi hb⟩

end Blotto.PlayerSpecificOverlapTableSourceCost
