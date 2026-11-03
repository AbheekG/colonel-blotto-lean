import Blotto.GeneralPaperProfitPointPrice

/-! Array overhead under a derived local control word. Arithmetic and bit
interpretations differ in their index primitive, while sharing array data.
-/
namespace Blotto.GeneralPaperControlArrayPrice
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem overhead (index : ℕ → ℕ) (W n k : ℕ) (hW : 1≤W) (hk : k≤n)
    (hIndex : ∀ i≤n,index (binaryWordWidth (i+1))≤W) :
    PaperIndexedArrayConstruction.overhead index W n k≤44*(k+1)*W := by
  have hn := hIndex n (Nat.le_refl _)
  induction k with
  | zero =>
    simp only [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.initialWork]
    nlinarith only [hn,hW]
  | succ k ih =>
    have hi := ih (by omega)
    have hs := hIndex k (by omega)
    simp only [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.stepWork]
    nlinarith only [hi,hs,hW]

theorem indexed_work {α : Type*} {n : ℕ} (index : ℕ → ℕ) (W C : ℕ) (callback : Fin n → α × ℕ)
    (hW : 1≤W) (hIndex : ∀ i≤n,index (binaryWordWidth (i+1))≤W) (hC : ∀ i,(callback i).2≤C) :
    (PaperIndexedArrayConstruction.run index W callback).2≤n*C+44*(n+1)*W := by
  rw [PaperIndexedArrayConstruction.run_work]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hC i)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  exact Nat.add_le_add hs (overhead index W n n hW (Nat.le_refl _) hIndex)

theorem list_work {α : Type*} (index : ℕ → ℕ) (W : ℕ) (xs : List α) (hW : 1≤W)
    (hIndex : ∀ i≤xs.length,index (binaryWordWidth (i+1))≤W) :
    (PaperListReferenceArray.run index W xs).2≤64*(xs.length+1)*W := by
  have hr := PaperListReferenceArray.into_work index W xs.length (50*W) xs #[] (by simp)
    (by
      intro i hi
      have hw := hIndex i hi
      unfold PaperIndexedArrayConstruction.stepWork
      nlinarith only [hw,hW])
  have hn := hIndex xs.length (Nat.le_refl _)
  change (PaperListReferenceArray.into index W xs #[]).2+
    PaperIndexedArrayConstruction.initialWork index W xs.length+(8*xs.length+8)*W≤_
  unfold PaperIndexedArrayConstruction.initialWork
  nlinarith only [hr,hn,hW]

end Blotto.GeneralPaperControlArrayPrice
