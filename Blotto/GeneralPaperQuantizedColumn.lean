import Blotto.GeneralPaperBlockQuantization

/-! A processed column stores only its original-row labels and K anchors.
Sorting and inverse-scatter tables are consumed while building these arrays.
-/
namespace Blotto.GeneralPaperQuantizedColumn
open GeneralPaperRowSort GeneralPaperQuantileBlocks GeneralPaperBlockQuantization
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Column (T K : ℕ) where
  labels : FixedArrayTable T (Fin K)
  anchors : FixedArrayTable K ℚ

def build {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) : Column (K*B) K :=
  let permutation := GeneralPaperRowSort.build (Nat.mul_pos hK hB) value
  let labels := FixedArrayTable.ofFn (fun i => block hB (permutation.inverse.read i))
  let anchors := FixedArrayTable.ofFn (anchor hB (fun r => value.read (permutation.forward.read r)))
  ⟨labels,anchors⟩

theorem build_label {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) (i : Fin (K*B)) :
    (build hK hB value).labels.read i=block hB ((GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).inverse.read i) :=
  FixedArrayTable.read_ofFn _ _

theorem build_anchor {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) :
    (build hK hB value).anchors.read l=anchor hB
      (fun r => value.read ((GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).forward.read r)) l :=
  FixedArrayTable.read_ofFn _ _

def bid {T K : ℕ} (column : Column T K) (i : Fin T) : ℚ := column.anchors.read (column.labels.read i)

theorem build_bid {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) (i : Fin (K*B)) :
    bid (build hK hB value) i=rounded hB
      (fun r => value.read ((GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).forward.read r))
      ((GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).inverse.read i) := by
  unfold bid rounded
  rw [build_anchor,build_label]

theorem label_count {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) :
    (Finset.univ.filter (fun i => (build hK hB value).labels.read i=l)).card=B := by
  simp_rw [build_label]
  let p := GeneralPaperRowSort.build (Nat.mul_pos hK hB) value
  exact permuted_block_card hB p.inverse.read p.inverse_injective p.inverse_surjective l

theorem zero_anchor {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) :
    (build hK hB value).anchors.read ⟨0,hK⟩=0 := by
  rw [build_anchor]
  exact anchor_zero hB hK _

theorem anchors_nonnegative {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ)
    (hNonnegative : ∀ i,0≤value.read i) (l : Fin K) : 0≤(build hK hB value).anchors.read l := by
  rw [build_anchor]
  exact anchor_nonnegative hB _ (fun _ => hNonnegative _) l

theorem anchors_ordered {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ)
    (hNonnegative : ∀ i,0≤value.read i) : Monotone (build hK hB value).anchors.read := by
  intro a b hab
  rw [build_anchor,build_anchor]
  exact anchor_mono hB _ (GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).ordered
    (fun _ => hNonnegative _) hab

theorem bid_nonnegative {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ)
    (hNonnegative : ∀ i,0≤value.read i) (i : Fin (K*B)) : 0≤bid (build hK hB value) i :=
  anchors_nonnegative hK hB value hNonnegative _

theorem bid_le_original {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ)
    (hNonnegative : ∀ i,0≤value.read i) (i : Fin (K*B)) : bid (build hK hB value) i≤value.read i := by
  rw [build_bid]
  have h := rounded_le hB _ (Sorted.ordered (GeneralPaperRowSort.build (Nat.mul_pos hK hB) value))
    (fun _ => hNonnegative _) ((GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).inverse.read i)
  simpa only [Sorted.forward_inverse] using h

theorem bid_event_count {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ)
    (P : ℚ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (bid (build hK hB value) i))).card=
      (Finset.univ.filter (fun r => P (rounded hB
        (fun r => value.read ((GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).forward.read r)) r))).card := by
  simp_rw [build_bid]
  let p := GeneralPaperRowSort.build (Nat.mul_pos hK hB) value
  exact permutation_filter_card p.inverse.read p.inverse_injective p.inverse_surjective
    (fun r => P (rounded hB (fun r => value.read (p.forward.read r)) r))

theorem original_event_count {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ)
    (P : ℚ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (value.read i))).card=
      (Finset.univ.filter (fun r => P (value.read
        ((GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).forward.read r)))).card := by
  let p := GeneralPaperRowSort.build (Nat.mul_pos hK hB) value
  have h := permutation_filter_card p.inverse.read p.inverse_injective p.inverse_surjective
    (fun r => P (value.read (p.forward.read r)))
  simpa only [p.forward_inverse] using h

theorem bid_event_upper {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ)
    (P : ℚ → Prop) [DecidablePred P] (hDown : ∀ a b,a≤b → P b → P a) :
    (Finset.univ.filter (fun i => P (bid (build hK hB value) i))).card ≤
      (Finset.univ.filter (fun i => P (value.read i))).card+B := by
  rw [bid_event_count,original_event_count hK hB]
  exact event_count_upper hB _ (GeneralPaperRowSort.build (Nat.mul_pos hK hB) value).ordered P hDown

end Blotto.GeneralPaperQuantizedColumn
