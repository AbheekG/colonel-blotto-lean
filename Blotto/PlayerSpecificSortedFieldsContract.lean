import Blotto.PlayerSpecificSortedFieldsExecution

/-! Complete finite-bit preparation of the exact sorted rational field row,
from original encoded input sizes. Input tables, measured controls, native
stable ratio sort, materialized coordinates and caller copies are joined. -/
namespace Blotto.PlayerSpecificSortedFieldsContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificSortedFieldsExecution PlayerSpecificBitRatioSortBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem total_profile (N R first second measured sorted fields copied frame : ℕ)
    (hf : first≤10000*(N+1)*R) (hs : second≤10000*(N+1)*R)
    (hm : measured≤512*(N+1)*R) (hso : sorted≤2000000*(N+1)^3*R)
    (hfields : fields≤2000*(N+1)^2*R) (hc : copied≤(9*N+3)*R)
    (hframe : frame≤4096*(N+1)*R) :
    first+second+measured+sorted+fields+copied+frame≤5000000*(N+1)^3*R := by
  have hlin : N+1≤(N+1)^3 := by nlinarith only [Nat.zero_le (N^3)]
  have hquad : (N+1)^2≤(N+1)^3 := by nlinarith only [Nat.zero_le (N^3)]
  have hlp:=Nat.mul_le_mul_right (25000*R) hlin
  have hqp:=Nat.mul_le_mul_right (2000*R) hquad
  have hr : 0≤(N+1)^3*R := Nat.zero_le _
  nlinarith only [hf,hs,hm,hso,hfields,hc,hframe,hlp,hqp,hr]

theorem source_cost {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (run model i).2≤5000000*(N+1)^3*
      model.rat (width N (PlayerSpecificRecognitionInputHeights.inputHeight i)) := by
  let L:=PlayerSpecificRecognitionInputHeights.inputHeight i
  let first:=PlayerSpecificInputArrayExecution.run model i.valuesA.weight
  let second:=PlayerSpecificInputArrayExecution.run model i.valuesB.weight
  let A:=PlayerSpecificBitRatioSortExecution.address model (PlayerSpecificWidthExecution.run model (N+1)).1
  let sorted:=PlayerSpecificBitRatioSortExecution.run model first.1 second.1
  have hi:=PlayerSpecificRecognitionInputHeights.original_fields i
  have hv : ∀ j,RationalHeight (first.1.read j) L := by
    intro j
    rw [PlayerSpecificInputArrayExecution.value,FixedArrayTable.read_ofFn]
    exact hi.2.1 j
  have hw : ∀ j,RationalHeight (second.1.read j) L := by
    intro j
    rw [PlayerSpecificInputArrayExecution.value,FixedArrayTable.read_ofFn]
    exact hi.2.2 j
  have hfirst:=PlayerSpecificInputArrayExecution.source_cost model L i.valuesA.weight hi.2.1
  have hsecond:=PlayerSpecificInputArrayExecution.source_cost model L i.valuesB.weight hi.2.2
  have hmeasure:=measurement_cost model N L
  have hsort:=PlayerSpecificBitRatioSortCost.source_cost model L first.1 second.1 hv hw
  have hids : sorted.1.data.toList.length=N := by simpa only [Array.length_toList] using sorted.1.size
  have hA:= (measured_bounds model N L).2.1
  have hfields:=PlayerSpecificFieldMaterializationCost.source_cost model A L first.1 second.1 hv hw hA sorted.1.data.toList (by omega)
  rw [hids] at hfields
  have hheight:=heights model i
  have hlen:=length model i
  have hcopy:=price_bound model (width N L) (by unfold width; omega) _
    (PlayerSpecificSweepTraceFits.copy_fields_fits (run model i).1 L (width N L) hheight
      (by unfold width; omega) (by rw [hlen]; unfold width; omega) (by unfold width; omega))
  rw [PlayerSpecificSweepExecution.copy_fields_length,hlen] at hcopy
  have hcopyp : price model (PlayerSpecificSweepExecution.copyFields (run model i).1)≤(9*N+3)*model.rat (width N L) := by
    nlinarith only [hcopy]
  have hframe : 64*(N+1)*A≤4096*(N+1)*model.rat (width N L) := by
    have hm:=Nat.mul_le_mul_left (64*(N+1)) hA
    nlinarith only [hm]
  simp only [run] at hcopyp ⊢
  exact total_profile N _ _ _ _ _ _ _ _ hfirst hsecond hmeasure hsort hfields hcopyp hframe

theorem actual_contract {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    let result:=run model i
    result.1=PlayerSpecificRationalIntervals.fields i ∧ result.1.length=N ∧
      PlayerSpecificRationalSweepHeights.FieldsHeight result.1 (PlayerSpecificRecognitionInputHeights.inputHeight i) ∧
      result.2≤5000000*(N+1)^3*model.rat (width N (PlayerSpecificRecognitionInputHeights.inputHeight i)) :=
  ⟨value model i,length model i,heights model i,source_cost model i⟩

end Blotto.PlayerSpecificSortedFieldsContract
