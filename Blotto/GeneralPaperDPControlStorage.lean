import Blotto.GeneralPaperStreamingScatterStorage

/-! One native label list is shared by both merge loop dimensions. Dense
empty-table construction includes every reserved slot at each prefix.
Finite labels and retained cardinalities supply all loop-control words. -/
namespace Blotto.GeneralPaperDPControlStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperEncodedFixedVector
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def labelsProfile (W n : ℕ) : ℕ := n*(rankWord n+2*W)+32*W

theorem labels (index : ℕ → ℕ) (W A n : ℕ) :
    GeneralPaperEncodedLabelStorage.listFootprint W (GeneralPaperDPTableControls.labels index W A n).1≤labelsProfile W n := by
  rw [GeneralPaperDPTableControls.labels_data]
  exact GeneralPaperEncodedLabelStorage.list_bound W n _ (by rw [List.length_finRange])

theorem labels_suffix_step {n : ℕ} (remaining : ℕ) (suffix : List (Fin n))
    (h : remaining+1+suffix.length=n) (i : Fin n) : remaining+(i::suffix).length=n := by
  rw [List.length_cons]
  omega

theorem labels_fill {n : ℕ} (index : ℕ → ℕ) (W A remaining : ℕ) (h : remaining≤n)
    (suffix : List (Fin n)) (hn : remaining+suffix.length=n) :
    GeneralPaperEncodedLabelStorage.listFootprint W
      (GeneralPaperIndexedListPrice.fill index A (fun i : Fin n => (i,64*W)) remaining h suffix).1≤labelsProfile W n := by
  apply GeneralPaperEncodedLabelStorage.list_bound
  rw [GeneralPaperIndexedListPrice.every_prefix,hn]

def slotBits {Witness : Type*} (W : ℕ) (encode : Witness → ℕ) : Option (Selection Tag Witness) → ℕ
  | none => 1
  | some chosen => rationalWordWidth chosen.cost.threshold+2+encode chosen.predecessor+32*W

theorem empty_prefix {Witness : Type*} (index : ℕ → ℕ) (W A J count : ℕ) (hc : count≤J) (encode : Witness → ℕ) :
    GeneralPaperEncodedReferenceVector.reservedFootprint W J (slotBits W encode)
      (PaperIndexedArrayConstruction.fill index A
        (fun _ : Fin J => ((none : Option (Selection Tag Witness)),64*W)) count hc).1≤J*(1+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index A W 1 (slotBits W encode) _
    (fun _ => Nat.le_refl _) count hc

def frame (W K J : ℕ) : ℕ := 256*W+8*(rankWord K+rankWord J)+64

theorem controls {K J : ℕ} (W : ℕ) (i : Fin K) (j : Fin J) :
    rankBits i+rankBits j+GeneralPaperEncodedScalarStorage.natBits K+
      GeneralPaperEncodedScalarStorage.natBits J+64*W≤frame W K J := by
  have hi := rank_bound i
  have hj := rank_bound j
  unfold frame GeneralPaperEncodedScalarStorage.natBits rankWord at *
  omega

theorem shared_labels (index : ℕ → ℕ) (W A J : ℕ) :
    GeneralPaperEncodedLabelStorage.listFootprint W (GeneralPaperDPTableControls.labels index W A J).1+2*W≤labelsProfile W J+2*W :=
  Nat.add_le_add_right (labels index W A J) _

end Blotto.GeneralPaperDPControlStorage
