import Blotto.GeneralPaperNativeEndpointColumns

/-! Physical endpoint columns decode to the exact compiler dictionary,
retaining the original stored label arrays. Contracts below are erased
semantic/size proofs, not runtime dictionaries or entry-cost oracles. -/
namespace Blotto.GeneralPaperNativeEndpointColumnLaw
open GeneralPaperSourceEndpointBranch
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem data {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    GeneralPaperRowQuantizer.dictionary (GeneralPaperNativeEndpointColumns.run price index A choice columns).1=
      GeneralPaperEndpointDictionary.dictionary ⟨(GeneralPaperRowQuantizer.dictionary columns).label,choice⟩ := by
  rw [GeneralPaperNativeEndpointColumns.data]
  unfold GeneralPaperRowQuantizer.dictionary GeneralPaperEndpointDictionary.dictionary
  congr 1
  · funext i j
    rw [FixedArrayTable.read_ofFn]
  · funext j l
    rw [FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact GeneralPaperNativeEndpointAnchor.data price A _ choice j l

theorem dictionary_models {T m K : ℕ} (price price' index index' : ℕ → ℕ) (A A' : ℕ)
    (choice : Choice (m*(K-1))) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    GeneralPaperRowQuantizer.dictionary (GeneralPaperNativeEndpointColumns.run price index A choice columns).1=
      GeneralPaperRowQuantizer.dictionary (GeneralPaperNativeEndpointColumns.run price' index' A' choice columns).1 := by rw [data,data]

theorem result_data {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (result : Result T m K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hLabels : (GeneralPaperRowQuantizer.dictionary columns).label=result.labels) :
    GeneralPaperRowQuantizer.dictionary (GeneralPaperNativeEndpointColumns.run price index A result.choice columns).1=
      GeneralPaperEndpointDictionary.dictionary result := by
  rw [data,hLabels]

theorem unit {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (result : Result T m K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hLabels : (GeneralPaperRowQuantizer.dictionary columns).label=result.labels) (hT : 0<T) (hK : 0<K)
    (h : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperEndpointDictionary.dictionary result) hT hK) :
    GeneralPaperTransferPreparation.UnitDictionary
      (GeneralPaperRowQuantizer.dictionary (GeneralPaperNativeEndpointColumns.run price index A result.choice columns).1) hT hK := by
  rw [result_data price index A result columns hLabels]
  exact h

theorem height {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (result : Result T m K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (H : ℕ)
    (h : ∀ j l,RationalHeight ((GeneralPaperEndpointDictionary.dictionary result).anchor j l) H) (j : Fin m) (l : Fin K) :
    RationalHeight (((GeneralPaperNativeEndpointColumns.run price index A result.choice columns).1.read j).anchors.read l) H := by
  rw [GeneralPaperNativeEndpointColumns.data,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  rw [GeneralPaperNativeEndpointAnchor.data price A result.labels result.choice]
  exact h j l

end Blotto.GeneralPaperNativeEndpointColumnLaw
