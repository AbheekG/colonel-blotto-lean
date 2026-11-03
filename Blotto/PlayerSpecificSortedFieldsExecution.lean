import Blotto.PlayerSpecificFieldMaterializationCost

/-! Actual finite-bit input-table construction, stable ratio sorting and
sorted rational-field materialization. Numerical output is exactly the
preserved rational interval caller's field row. -/
namespace Blotto.PlayerSpecificSortedFieldsExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) : List (ℚ×ℚ)×ℕ :=
  let first:=PlayerSpecificInputArrayExecution.run model i.valuesA.weight
  let second:=PlayerSpecificInputArrayExecution.run model i.valuesB.weight
  let measured:=PlayerSpecificWidthExecution.run model (N+1)
  let A:=PlayerSpecificBitRatioSortExecution.address model measured.1
  let sorted:=PlayerSpecificBitRatioSortExecution.run model first.1 second.1
  let fields:=PlayerSpecificFieldMaterializationExecution.run model A first.1 second.1 sorted.1.data.toList
  (fields.1,first.2+second.2+measured.2+sorted.2+fields.2+
    price model (PlayerSpecificSweepExecution.copyFields fields.1)+64*(N+1)*A)

theorem value {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (run model i).1=PlayerSpecificRationalIntervals.fields i := by
  simp only [run,PlayerSpecificFieldMaterializationExecution.value,PlayerSpecificInputArrayExecution.value,
    PlayerSpecificBitRatioSortExecution.value,FixedArrayTable.read_ofFn]
  rfl

theorem length {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) : (run model i).1.length=N := by
  rw [value,PlayerSpecificRationalIntervals.fields_length]

theorem heights {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    PlayerSpecificRationalSweepHeights.FieldsHeight (run model i).1 (PlayerSpecificRecognitionInputHeights.inputHeight i) := by
  rw [value]
  exact PlayerSpecificRecognitionInputHeights.sorted_fields i

end Blotto.PlayerSpecificSortedFieldsExecution
