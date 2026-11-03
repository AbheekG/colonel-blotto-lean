import Blotto.GeneralPaperNativeEndpointAnchor

/-! Replace only the anchors of retained physical unit columns with the
selected endpoint's packed point or immediate zero tag. Original labels
are retained by reference, with one materialization per field and label. -/
namespace Blotto.GeneralPaperNativeEndpointColumns
open GeneralPaperSourceEndpointBranch
set_option autoImplicit false
set_option maxHeartbeats 2200000

def field {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (choice : Choice (m*(K-1)))
    (old : GeneralPaperQuantizedColumn.Column T K) (j : Fin m) : GeneralPaperQuantizedColumn.Column T K×ℕ :=
  let anchors := PaperIndexedArrayConstruction.run index A (fun l => GeneralPaperNativeEndpointAnchor.run price A choice j l)
  (⟨old.labels,anchors.1⟩,anchors.2+64*A)

def run {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun j => field price index A choice (columns.read j) j)

theorem data {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    (run price index A choice columns).1=FixedArrayTable.ofFn (fun j =>
      (⟨(columns.read j).labels,FixedArrayTable.ofFn (fun l => (GeneralPaperNativeEndpointAnchor.run price A choice j l).1)⟩ :
        GeneralPaperQuantizedColumn.Column T K)) := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  dsimp only [field]
  rw [PaperIndexedArrayConstruction.run_data]

theorem work {T m K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A : ℕ) (hA : 1≤A)
    (choice : Choice (m*(K-1))) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hIndex : ∀ i≤m+K,index (binaryWordWidth (i+1))≤A) :
    (run price index A choice columns).2≤
      m*(K*(9*price (GeneralPaperNativeEndpointAnchor.width m K)+128*A)+44*(K+1)*A+64*A)+44*(m+1)*A := by
  apply GeneralPaperControlArrayPrice.indexed_work index A _ _ hA (fun i hi => hIndex i (by omega))
  intro j
  have h := GeneralPaperControlArrayPrice.indexed_work index A _
    (fun l => GeneralPaperNativeEndpointAnchor.run price A choice j l) hA (fun i hi => hIndex i (by omega))
    (GeneralPaperNativeEndpointAnchor.work price hMono A choice j)
  exact Nat.add_le_add_right h (64*A)

end Blotto.GeneralPaperNativeEndpointColumns
