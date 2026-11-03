import Blotto.GeneralPaperNativeBlockLabel

/-! Scatter computed occurrence-block labels to the original row keys.
This consumes the actual stored stable order, without searching an inverse
permutation. Repeated rational values retain their original row identities. -/
namespace Blotto.GeneralPaperNativeQuantizedLabels
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem table_ext {T : ℕ} {α : Type*} (a b : FixedArrayTable T α) (h : ∀ i,a.read i=b.read i) : a=b := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      congr 1
      apply Array.ext (ha.trans hb.symm)
      intro i hi hj
      exact h ⟨i,by omega⟩

def entry {K B : ℕ} (price : ℕ → ℕ) (A : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (r : Fin (K*B)) : (Fin (K*B)×Fin K)×ℕ :=
  let label := GeneralPaperNativeBlockLabel.run price A hB r
  ((order.read r,label.1),label.2+64*A)

def run {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) : FixedArrayTable (K*B) (Fin K)×ℕ :=
  GeneralPaperIndexedScatter.run index A ⟨0,hK⟩ (entry price A hB order)

theorem read_rank {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (hInjective : Function.Injective order.read) (r : Fin (K*B)) :
    (run price index A hK hB order).1.read (order.read r)=GeneralPaperQuantileBlocks.block hB r := by
  have h := GeneralPaperIndexedScatter.read_at index A ⟨0,hK⟩ (entry price A hB order) hInjective r
  simpa only [run,entry,GeneralPaperNativeBlockLabel.data] using h

theorem data {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) :
    (run price index A hK hB (GeneralPaperNativeRepresentativeSort.run price index A value).1).1=
      (GeneralPaperQuantizedColumn.build hK hB value).labels := by
  rw [GeneralPaperNativeRepresentativeSort.data]
  apply table_ext
  intro i
  let p := GeneralPaperRowSort.build (Nat.mul_pos hK hB) value
  have h := read_rank price index A hK hB (GeneralPaperRowSort.order value)
    (GeneralPaperRowSort.order_injective value) (p.inverse.read i)
  change (run price index A hK hB p.forward).1.read (p.forward.read (p.inverse.read i))=_ at h
  rw [p.forward_inverse] at h
  change (run price index A hK hB p.forward).1.read i=_
  rw [h,GeneralPaperQuantizedColumn.build_label]

theorem work {K B : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A : ℕ) (hA : 1≤A)
    (hK : 0<K) (hB : 0<B) (order : FixedArrayTable (K*B) (Fin (K*B)))
    (hIndex : ∀ i≤2*(K*B),index (binaryWordWidth (i+1))≤A) :
    (run price index A hK hB order).2≤
      (K*B)*(512*(binaryWordWidth (K*B)+1)*(A+price (GeneralPaperNativeBlockLabel.width (K*B) B))+64*A)+
      192*(2*(K*B)+1)*A := by
  have h := GeneralPaperIndexedScatter.work index A _ hA ⟨0,hK⟩ (entry price A hB order)
    (fun r => Nat.add_le_add_right (GeneralPaperNativeBlockLabel.work price hMono A hB r) (64*A))
    (fun i hi => hIndex i (by omega))
  simpa only [run,two_mul] using h

end Blotto.GeneralPaperNativeQuantizedLabels
