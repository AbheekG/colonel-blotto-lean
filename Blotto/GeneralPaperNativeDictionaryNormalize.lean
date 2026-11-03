import Blotto.GeneralPaperNativeQuantizedMatrix

/-! Scale stored column anchors once, retaining each original label array
by reference. Unit normalization computes the rational reciprocal once.
No functional dictionary is accepted as an unpriced native reader. -/
namespace Blotto.GeneralPaperNativeDictionaryNormalize
set_option autoImplicit false
set_option maxHeartbeats 2200000

def scale {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun j =>
    let old := columns.read j
    let anchors := GeneralPaperRationalOutputScale.run price index A c old.anchors
    (⟨old.labels,anchors.1⟩,anchors.2+96*A))

theorem scale_data {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    (scale price index A c columns).1=FixedArrayTable.ofFn (fun j =>
      (⟨(columns.read j).labels,FixedArrayTable.ofFn (fun l => c*(columns.read j).anchors.read l)⟩ : GeneralPaperQuantizedColumn.Column T K)) := by
  unfold scale
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  dsimp only
  rw [GeneralPaperRationalOutputScale.data]

theorem dictionary_scale {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    GeneralPaperRowQuantizer.dictionary (scale price index A c columns).1=
      GeneralPaperDictionary.scale (GeneralPaperRowQuantizer.dictionary columns) c := by
  rw [scale_data]
  unfold GeneralPaperRowQuantizer.dictionary GeneralPaperDictionary.scale
  simp only [FixedArrayTable.read_ofFn]

theorem scale_work {T m K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A C H : ℕ) (hA : 1≤A)
    (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hc : RationalHeight c C)
    (h : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hIndex : ∀ i≤m+K,index (binaryWordWidth (i+1))≤A) :
    (scale price index A c columns).2≤m*(K*(2*price (1+2*(C+H))+64*A)+44*(K+1)*A+96*A)+44*(m+1)*A :=
  GeneralPaperControlArrayPrice.indexed_work index A _ _ hA (fun i hi => hIndex i (by omega))
    (fun j => Nat.add_le_add_right (GeneralPaperRationalOutputScale.work price index hMono A C H hA c
      (columns.read j).anchors hc (h j) (fun i hi => hIndex i (by omega))) (96*A))

def run {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×ℕ :=
  let inverse := budget⁻¹
  let result := scale price index A inverse columns
  (result.1,result.2+GeneralPaperRationalPrimitivePrice.unary price (fun x => x⁻¹) budget+32*A)

theorem data {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    GeneralPaperRowQuantizer.dictionary (run price index A budget columns).1=
      GeneralPaperDictionary.normalize (GeneralPaperRowQuantizer.dictionary columns) budget :=
  dictionary_scale price index A budget⁻¹ columns

theorem work {T m K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A C H : ℕ) (hA : 1≤A)
    (budget : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hc : RationalHeight budget C)
    (h : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hIndex : ∀ i≤m+K,index (binaryWordWidth (i+1))≤A) :
    (run price index A budget columns).2≤m*(K*(2*price (1+2*(C+H))+64*A)+44*(K+1)*A+96*A)+44*(m+1)*A+
      2*price (1+2*C)+32*A := by
  have hs := scale_work price index hMono A C H hA budget⁻¹ columns hc.inv h hIndex
  have hi := GeneralPaperRationalPrimitivePrice.unary_le price hMono (fun x => x⁻¹) budget (1+2*C)
    (rationalWordWidth_of_height hc) (rationalWordWidth_of_height hc.inv)
  unfold run
  dsimp only
  omega

theorem height {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (C H : ℕ) (hc : RationalHeight budget C)
    (h : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H) (j : Fin m) (l : Fin K) :
    RationalHeight (((run price index A budget columns).1.read j).anchors.read l) (C+H) := by
  change RationalHeight (((scale price index A budget⁻¹ columns).1.read j).anchors.read l) _
  rw [scale_data,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  exact hc.inv.mul (h j l)

end Blotto.GeneralPaperNativeDictionaryNormalize
