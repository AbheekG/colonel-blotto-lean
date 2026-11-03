import Blotto.GeneralPaperNativePayloadFillStorage

/-! The same literal indexed-fill lifetime, bounded by the sum of owned
payloads instead of n times their largest size. Zero-payload frames retain
all original control/work fields; only their element payload is separated.
This is an erased analysis of the existing fill, not a new implementation. -/
namespace Blotto.GeneralPaperAdditivePayloadFillStorage
open GeneralPaperNativePayloadFillStorage GeneralPaperEncodedScalarStorage
open PaperIndexedArrayConstruction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def prefixPayload {α : Type*} {n : ℕ} (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) : ℕ :=
  ∑ i : Fin k, encode (callback ⟨i.val, by omega⟩).1

theorem prefix_succ {α : Type*} {n : ℕ} (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k + 1 ≤ n) :
    prefixPayload encode callback (k + 1) hk =
      prefixPayload encode callback k (by omega) + encode (callback ⟨k, by omega⟩).1 := by
  unfold prefixPayload
  rw [Fin.sum_univ_castSucc]
  rfl

theorem prefix_le {α : Type*} {n : ℕ} (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) :
    prefixPayload encode callback k hk ≤ ∑ i : Fin n, encode (callback i).1 := by
  unfold prefixPayload
  apply Finset.sum_le_sum_of_injOn (fun i : Fin k => (⟨i.val, by omega⟩ : Fin n))
  · intro i _ j _ h; exact Fin.ext (congrArg (fun x : Fin n => x.val) h)
  · exact Finset.subset_univ _
  · intro i _; exact le_rfl
  · intro i _ _; exact Nat.zero_le _

theorem frames_split {α : Type*} {n : ℕ} (W : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) :
    frames W encode callback k hk = prefixPayload encode callback k hk +
      frames W (fun _ => 0) callback k hk := by
  induction k with
  | zero => simp only [frames, frame, prefixPayload, Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_add]
  | succ k ih =>
    rw [frames, frames, ih, prefix_succ]
    simp only [frame, Nat.zero_add]
    omega

theorem frames_bound {α : Type*} {n : ℕ} (W S C : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (hs : (∑ i : Fin n, encode (callback i).1) ≤ S)
    (hc : ∀ i, (callback i).2 ≤ C) (hW : 1 ≤ W)
    (hIndex : binaryWordWidth (n + 1) ≤ W) (k : ℕ) (hk : k ≤ n) :
    frames W encode callback k hk ≤ S + (k + 1) * frameProfile W 0 n C := by
  rw [frames_split]
  exact Nat.add_le_add ((prefix_le encode callback k hk).trans hs)
    (GeneralPaperNativePayloadFillStorage.frames_bound W 0 C (fun _ => 0) callback
      (fun _ => le_rfl) hc hW hIndex k hk)

theorem buffer_bound {α : Type*} {n : ℕ} (W S : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (hs : (∑ i : Fin n, encode (callback i).1) ≤ S)
    (k : ℕ) (hk : k ≤ n) :
    GeneralPaperEncodedReferenceVector.reservedFootprint W n encode
      (fill (fun w => w) W callback k hk).1 ≤ S + n * W + 64 * W := by
  rw [fill_data]
  have hp := (prefix_le encode callback k hk).trans hs
  have he : GeneralPaperEncodedReferenceVector.payload encode
      (Array.ofFn (fun i : Fin k => (callback ⟨i.val, by omega⟩).1)) =
      prefixPayload encode callback k hk := by
    unfold GeneralPaperEncodedReferenceVector.payload prefixPayload
    apply Finset.sum_bij (fun i _ => (⟨i.val, by simpa only [Array.size_ofFn] using i.isLt⟩ : Fin k))
    · intro i _; exact Finset.mem_univ _
    · intro i _ j _ h; exact Fin.ext (congrArg (fun x : Fin k => x.val) h)
    · intro j _
      refine ⟨⟨j.val, by simpa only [Array.size_ofFn] using j.isLt⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro i _; rw [Array.getElem_ofFn]
  change GeneralPaperEncodedReferenceVector.payload encode _ + n * W + 64 * W ≤ _
  rw [he]
  omega

theorem returned_bound {α : Type*} {n : ℕ} (W S : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (hs : (∑ i : Fin n, encode (callback i).1) ≤ S) :
    GeneralPaperEncodedBasisStorage.arrayFootprint W encode
      (run (fun w => w) W callback).1 ≤ S + n * W + 64 * W := by
  unfold GeneralPaperEncodedBasisStorage.arrayFootprint
  simp only [run_data, FixedArrayTable.read_ofFn, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

def profile (W S P n C Q : ℕ) : ℕ :=
  3 * (S + n * W + 64 * W) + S + (n + 1) * frameProfile W 0 n C +
    P + Q + 5 * (natBits (metadataCap W n C) + W) + 224 * W

theorem bounded {α : Type*} {n : ℕ} (W S P C Q : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (space : Fin n → ℕ)
    (hs : (∑ i : Fin n, encode (callback i).1) ≤ S)
    (hp : ∀ i, encode (callback i).1 ≤ P) (hc : ∀ i, (callback i).2 ≤ C)
    (hq : ∀ i, space i ≤ Q) (hW : 1 ≤ W) (hIndex : binaryWordWidth (n + 1) ≤ W)
    (k : ℕ) (hk : k ≤ n) :
    window W encode callback space k hk ≤ profile W S P n C Q := by
  have hBuffer := buffer_bound W S encode callback hs k hk
  have hReturned := returned_bound W S encode callback hs
  have hFrames := (frames_bound W S C encode callback hs hc hW hIndex k hk).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right hk 1)) S)
  have hCurrent : current encode callback k ≤ P := by unfold current; split; exact hp _; omega
  have hActive : active space k ≤ Q := by unfold active; split; exact hq _; omega
  have hPartial := prefix_work W C callback hc hW hIndex k hk
  have hWork := prefix_work W C callback hc hW hIndex n le_rfl
  change (run (fun w => w) W callback).2 ≤ workCap W n C at hWork
  have hf := fields_bound W (natBits (metadataCap W n C))
    [n,k,k+1,(fill (fun w => w) W callback k hk).2,(run (fun w => w) W callback).2] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      all_goals unfold metadataCap; omega)
  change fields W _ ≤ 5 * (natBits (metadataCap W n C) + W) + 32 * W at hf
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperAdditivePayloadFillStorage
