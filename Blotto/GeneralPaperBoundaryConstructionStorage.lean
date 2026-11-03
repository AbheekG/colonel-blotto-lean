import Blotto.GeneralPaperCompleteFrontStorage
import Blotto.GeneralPaperGridArrayConstructionStorage

/-! Native adjacent-cell construction: full reserved old/new pair buffers,
boundary input, selected fill frames and current callback/control values.
Storage word A and the actual operation word W are kept distinct. -/
namespace Blotto.GeneralPaperBoundaryConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedPartitionStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def filledPrefix {n : ℕ} (index primitive : ℕ → ℕ) (W A : ℕ) (boundary : FixedArrayTable (n+1) ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint A n (pairBits A)
    (PaperIndexedArrayConstruction.fill index (GeneralPaperSummaryArrayExecution.arrayWord W n)
      (GeneralPaperBoundaryCellPrice.element primitive W boundary) count hc).1

theorem pair_word {n : ℕ} (primitive : ℕ → ℕ) (W A U : ℕ) (boundary : FixedArrayTable (n+1) ℕ)
    (hb : ∀ i,boundary.read i≤U) (r : Fin n) :
    pairBits A (GeneralPaperBoundaryCellPrice.element primitive W boundary r).1≤2*natBits U+8*A := by
  rw [GeneralPaperBoundaryCellPrice.element_data]
  have h0 := binaryWordWidth_mono (hb r.castSucc)
  have h1 := binaryWordWidth_mono (hb r.succ)
  unfold pairBits natBits
  dsimp only
  omega

theorem prefix_bound {n : ℕ} (index primitive : ℕ → ℕ) (W A U : ℕ) (boundary : FixedArrayTable (n+1) ℕ)
    (hb : ∀ i,boundary.read i≤U) (count : ℕ) (hc : count≤n) :
    filledPrefix index primitive W A boundary count hc≤n*(2*natBits U+9*A)+64*A := by
  have h := GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index
    (GeneralPaperSummaryArrayExecution.arrayWord W n) A (2*natBits U+8*A) (pairBits A)
    (GeneralPaperBoundaryCellPrice.element primitive W boundary) (pair_word primitive W A U boundary hb) count hc
  exact h.trans_eq (by ring)

theorem frames_mono (A n N : ℕ) (hn : n≤N) :
    GeneralPaperGridArrayConstructionStorage.frames A n≤GeneralPaperGridArrayConstructionStorage.frames A N := by
  have h := binaryWordWidth_mono (Nat.add_le_add_right hn 1)
  apply Nat.mul_le_mul (Nat.add_le_add_right hn 1)
  unfold natBits
  omega

def controls (A n count : ℕ) : ℕ := fields A [n,count,n+1,count+1]

theorem controls_bound (A n N count : ℕ) (hn : n≤N) (hc : count≤n) :
    controls A n count≤4*(natBits (N+1)+A)+32*A := by
  apply fields_bound A (natBits (N+1))
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> unfold natBits <;>
    exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1

def window {n : ℕ} (model : RationalCostModel) (W A U : ℕ) (boundary : FixedArrayTable (n+1) ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedNatArray.footprint A boundary+2*filledPrefix (fun w => w) model.rat W A boundary count hc+
    GeneralPaperGridArrayConstructionStorage.frames A n+controls A n count+2*natBits U+8*A+
      (GeneralPaperBoundaryCellPrice.run true (fun w => w) model.rat W boundary).2+128*A

def profile (model : RationalCostModel) (W A U N : ℕ) : ℕ :=
  let P := natBits U
  (N+1)*(P+A)+32*A+2*(N*(2*P+9*A)+64*A)+GeneralPaperGridArrayConstructionStorage.frames A N+
    4*(natBits (N+1)+A)+32*A+2*P+8*A+GeneralPaperBoundaryCellPrice.profile model.rat W N+128*A

theorem bounded {n : ℕ} (model : RationalCostModel) (W A U N : ℕ) (boundary : FixedArrayTable (n+1) ℕ)
    (hn : n≤N) (hb : ∀ i,boundary.read i≤U) (count : ℕ) (hc : count≤n) :
    window model W A U boundary count hc≤profile model W A U N := by
  have hinput := GeneralPaperEncodedNatArray.bounded_length A (natBits U) (N+1) boundary
    (Nat.add_le_add_right hn 1) (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hb i)) 1)
  have hp := (prefix_bound (fun w => w) model.rat W A U boundary hb count hc).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hf := frames_mono A n N hn
  have hcontrols := controls_bound A n N count hn hc
  have hs := (GeneralPaperBoundaryCellPrice.bit_work model.rat model.monotone W boundary).trans
    (GeneralPaperBoundaryCellPrice.profile_mono model.rat model.monotone W n N hn)
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperBoundaryConstructionStorage
