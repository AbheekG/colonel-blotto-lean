import Blotto.GeneralPaperNativeQuantizedLabels

/-! Construct only the K previous-block anchor references from the stored
sorted order. Label zero is zero. Each reached predecessor calculation and
array write is charged, with no rational payload copy in this phase. -/
namespace Blotto.GeneralPaperNativeQuantizedAnchors
set_option autoImplicit false
set_option maxHeartbeats 2000000

def entry {K B : ℕ} (price : ℕ → ℕ) (A : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) : ℚ×ℕ :=
  let test := GeneralPaperIntegerWordPrice.compare price l.val 0
  if l.val=0 then (0,test+64*A) else
    let product := l.val*B
    let previous := product-1
    let r : Fin (K*B) := ⟨previous,(GeneralPaperBlockQuantization.predecessor hB l).isLt⟩
    (value.read (order.read r),test+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) l.val B+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) product 1+64*A)

def run {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) : FixedArrayTable K ℚ×ℕ :=
  PaperIndexedArrayConstruction.run index A (entry price A hB order value)

theorem entry_data {K B : ℕ} (price : ℕ → ℕ) (A : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) :
    (entry price A hB order value l).1=GeneralPaperBlockQuantization.anchor hB (fun r => value.read (order.read r)) l := by
  unfold entry GeneralPaperBlockQuantization.anchor
  split <;> rfl

theorem data {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) :
    (run price index A hB (GeneralPaperNativeRepresentativeSort.run price index A value).1 value).1=
      (GeneralPaperQuantizedColumn.build hK hB value).anchors := by
  rw [GeneralPaperNativeRepresentativeSort.data]
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]
  apply GeneralPaperNativeQuantizedLabels.table_ext
  intro l
  rw [FixedArrayTable.read_ofFn,entry_data,GeneralPaperQuantizedColumn.build_anchor]
  rfl

theorem entry_work {K B : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (A : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) :
    (entry price A hB order value l).2≤5*price (1+binaryWordWidth (K*B+B+1))+64*A := by
  have ht := GeneralPaperIntegerWordPrice.compare_le price hMono l.val 0 (1+binaryWordWidth (K*B+B+1))
    (Nat.add_le_add_left (binaryWordWidth_mono (by nlinarith only [l.isLt,hB])) 1)
    (Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le _)) 1)
  have hm : l.val*B≤K*B+B+1 := by nlinarith only [l.isLt,hB]
  have hp := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) l.val B (K*B+B+1)
    (by nlinarith only [l.isLt,hB]) (by omega) hm
  have hs := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a-b) (l.val*B) 1 (K*B+B+1)
    hm (by omega) (by omega)
  unfold entry
  split <;> dsimp only <;> omega

theorem work {K B : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A : ℕ) (hA : 1≤A) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ)
    (hIndex : ∀ i≤K,index (binaryWordWidth (i+1))≤A) :
    (run price index A hB order value).2≤K*(5*price (1+binaryWordWidth (K*B+B+1))+64*A)+44*(K+1)*A :=
  GeneralPaperControlArrayPrice.indexed_work index A _ _ hA hIndex (entry_work price hMono A hB order value)

end Blotto.GeneralPaperNativeQuantizedAnchors
