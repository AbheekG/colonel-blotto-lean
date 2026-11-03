import Blotto.GeneralPaperRetainedEndpointBitBounds
import Blotto.GeneralPaperNativeEndpointColumnLaw

/-! Equality of retained native data across the arithmetic and bit price
models. These are erased refinements of actual arrays, including original
labels and every anchor, rather than equality of marginal output laws. -/
namespace Blotto.GeneralPaperRetainedBitData
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem dictionary_injective {T m K : ℕ} : Function.Injective
    (GeneralPaperRowQuantizer.dictionary (T:=T) (m:=m) (K:=K)) := by
  intro a b h
  apply GeneralPaperNativeQuantizedLabels.table_ext
  intro j
  have hl : (a.read j).labels=(b.read j).labels := by
    apply GeneralPaperNativeQuantizedLabels.table_ext
    intro i
    exact congrArg (fun d => d.label i j) h
  have ha : (a.read j).anchors=(b.read j).anchors := by
    apply GeneralPaperNativeQuantizedLabels.table_ext
    intro l
    exact congrArg (fun d => d.anchor j l) h
  exact congrArg₂ GeneralPaperQuantizedColumn.Column.mk hl ha

theorem endpoint_columns {T m K : ℕ} (price price' index index' : ℕ → ℕ) (W W' : ℕ)
    (choice : GeneralPaperSourceEndpointBranch.Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    (GeneralPaperNativeEndpointColumns.run price index W choice columns).1=
      (GeneralPaperNativeEndpointColumns.run price' index' W' choice columns).1 :=
  dictionary_injective (GeneralPaperNativeEndpointColumnLaw.dictionary_models price price' index index' W W' choice columns)

theorem unit_columns {T m K : ℕ} (price price' index index' : ℕ → ℕ) (W W' : ℕ)
    (hT : 0<T) (hK : 0<K) (hDiv : K∣T) (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    (GeneralPaperNativeUnitSourceJoin.run price index W hT hK hDiv budget rows).1=
      (GeneralPaperNativeUnitSourceJoin.run price' index' W' hT hK hDiv budget rows).1 :=
  dictionary_injective (GeneralPaperNativeUnitSourceJoin.dictionary_models price price' index index' W W' hT hK hDiv budget rows)

theorem values {m : ℕ} (model : RationalCostModel) (W Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : (∑ j,weights.read j)=Qv) :
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1=
      (GeneralPaperRetainedFieldValues.run false model 1 Qv hQv weights hp hs).1 := by
  have h := (GeneralPaperRetainedFieldValues.data true model W Qv hQv weights hp hs).trans
    (GeneralPaperRetainedFieldValues.data false model 1 Qv hQv weights hp hs).symm
  generalize ha : (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1=a at h ⊢
  generalize hb : (GeneralPaperRetainedFieldValues.run false model 1 Qv hQv weights hp hs).1=b at h ⊢
  cases a
  cases b
  congr 1

theorem transfer_output_ext {T m K S : ℕ} (a b : GeneralPaperRetainedTransferPreparation.Output T m K S)
    (hp : a.prepared=b.prepared) (hm : a.matrix=b.matrix) (hx : a.maximum=b.maximum) (hb : a.budget=b.budget) : a=b := by
  cases a
  cases b
  simp_all only

theorem transfer {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (hCap : S<2^depth) :
    (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1=
      (GeneralPaperRetainedTransferPreparation.run false model 1 depth S hK columns values own opposing).1 := by
  apply transfer_output_ext
  · rw [GeneralPaperRetainedTransferPreparation.data true model W depth S hK columns values own opposing hCap,
      GeneralPaperRetainedTransferPreparation.data false model 1 depth S hK columns values own opposing hCap]
  · rw [GeneralPaperRetainedTransferPreparation.matrix_data,GeneralPaperRetainedTransferPreparation.matrix_data,
      GeneralPaperPhysicalScoreMatrix.data true model W depth columns _ S hK hCap,
      GeneralPaperPhysicalScoreMatrix.data false model 1 depth columns _ S hK hCap]
  · rw [GeneralPaperRetainedTransferPreparation.maximum_data true model W depth S hK columns values own opposing hCap,
      GeneralPaperRetainedTransferPreparation.maximum_data false model 1 depth S hK columns values own opposing hCap]
  · rfl

end Blotto.GeneralPaperRetainedBitData
