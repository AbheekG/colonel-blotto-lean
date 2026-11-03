import Blotto.GeneralPaperNativeQuantizedColumn

/-! Native whole-table quantization. Each field column is materialized
from the retained source rows, processed once, and retained as label/anchor
arrays. Original whole-row identities are preserved through every field. -/
namespace Blotto.GeneralPaperNativeQuantizedMatrix
set_option autoImplicit false
set_option maxHeartbeats 2800000

def columnInput {T m : ℕ} (index : ℕ → ℕ) (A : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (j : Fin m) :
    FixedArrayTable T ℚ×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun i => ((rows.read i).read j,64*A))

theorem input_data {T m : ℕ} (index : ℕ → ℕ) (A : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (j : Fin m) :
    (columnInput index A rows j).1=GeneralPaperRowQuantizer.columnInput rows j := by
  unfold columnInput GeneralPaperRowQuantizer.columnInput
  rw [PaperIndexedArrayConstruction.run_data]

def field {K B m : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (j : Fin m) : GeneralPaperQuantizedColumn.Column (K*B) K×ℕ :=
  let input := columnInput index A rows j
  let column := GeneralPaperNativeQuantizedColumn.run price index A hK hB input.1
  (column.1,input.2+column.2+32*A)

theorem field_data {K B m : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (j : Fin m) :
    (field price index A hK hB rows j).1=GeneralPaperQuantizedColumn.build hK hB (GeneralPaperRowQuantizer.columnInput rows j) := by
  dsimp only [field]
  rw [GeneralPaperNativeQuantizedColumn.data,input_data]

def run {K B m : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) : FixedArrayTable m (GeneralPaperQuantizedColumn.Column (K*B) K)×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun j => let col := field price index A hK hB rows j; (col.1,col.2+64*A))

theorem data {K B m : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) :
    (run price index A hK hB rows).1=GeneralPaperRowQuantizer.prepare hK hB rows := by
  unfold run GeneralPaperRowQuantizer.prepare
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact field_data price index A hK hB rows j

theorem dictionary_data {K B m : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) :
    GeneralPaperRowQuantizer.dictionary (run price index A hK hB rows).1=GeneralPaperRowQuantizer.build hK hB rows := by
  rw [data]
  rfl

def fieldProfile (K B A sortPrice blockPrice anchorPrice : ℕ) : ℕ :=
  (K*B)*(64*A)+44*(K*B+1)*A+GeneralPaperNativeQuantizedColumn.profile K B A sortPrice blockPrice anchorPrice+32*A

theorem field_work {K B m : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A H : ℕ) (hA : 1≤A)
    (hK : 0<K) (hB : 0<B) (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ))
    (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤H)
    (hIndex : ∀ i≤2*(K*B)+K,index (binaryWordWidth (i+1))≤A) (j : Fin m) :
    (field price index A hK hB rows j).2≤fieldProfile K B A (price H)
      (price (GeneralPaperNativeBlockLabel.width (K*B) B)) (price (1+binaryWordWidth (K*B+B+1))) := by
  have hi := GeneralPaperControlArrayPrice.indexed_work index A (64*A) (fun i => ((rows.read i).read j,64*A)) hA
    (fun i hi => hIndex i (by omega)) (fun _ => le_rfl)
  have hc := GeneralPaperNativeQuantizedColumn.work price index hMono A H hA hK hB (columnInput index A rows j).1
    (by intro i;rw [input_data,GeneralPaperRowQuantizer.columnInput,FixedArrayTable.read_ofFn];exact hv i j) hIndex
  change (columnInput index A rows j).2≤_ at hi
  unfold field fieldProfile
  dsimp only
  omega

theorem work {K B m : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A H : ℕ) (hA : 1≤A)
    (hK : 0<K) (hB : 0<B) (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ))
    (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤H)
    (hIndex : ∀ i≤2*(K*B)+K+m,index (binaryWordWidth (i+1))≤A) :
    (run price index A hK hB rows).2≤m*(fieldProfile K B A (price H)
      (price (GeneralPaperNativeBlockLabel.width (K*B) B)) (price (1+binaryWordWidth (K*B+B+1)))+64*A)+44*(m+1)*A :=
  GeneralPaperControlArrayPrice.indexed_work index A _ _ hA (fun i hi => hIndex i (by omega))
    (fun j => Nat.add_le_add_right (field_work price index hMono A H hA hK hB rows hv
      (fun i hi => hIndex i (by omega)) j) (64*A))

end Blotto.GeneralPaperNativeQuantizedMatrix
