import Blotto.GeneralPaperReferenceCopy

/-! Executed sequential block layout with actual fixed-width references.
Temporary plan/list references use S; target block references use A. Each
allocation constructs its encoded pointer and prices cursor arithmetic.
Disjointness and capacity follow from the actual returned block schedule. -/
namespace Blotto.GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

structure Region (A : ℕ) where
  start : ℕ
  length : ℕ
  reference : FixedBinaryWord A

def Region.stop {A : ℕ} (r : Region A) : ℕ := r.start + r.length

def run (model : RationalCostModel) (S A : ℕ) : ℕ → List ℕ → List (Region A) × (ℕ × ℕ)
  | start, [] => ([],start,64 * (S + A + 1))
  | start, size :: sizes =>
    let encoded := GeneralPaperStoredWordEncoding.word model S A start
    let next := start + size
    let later := run model S A next sizes
    (⟨start,size,encoded.1⟩ :: later.1,later.2.1,
      encoded.2 + GeneralPaperEqualAddressConstruction.price model S start size next +
        later.2.2 + 64 * (S + A + 1))

theorem cursor (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) :
    (run model S A start sizes).2.1 = start + sizes.sum := by
  induction sizes generalizing start with
  | nil => rfl
  | cons size sizes ih => simp only [run,ih,List.sum_cons]; omega

theorem lengths (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) :
    ((run model S A start sizes).1.map Region.length) = sizes := by
  induction sizes generalizing start with
  | nil => rfl
  | cons size sizes ih => simp only [run,List.map_cons,ih]

theorem count (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) :
    (run model S A start sizes).1.length = sizes.length := by
  have h := congrArg List.length (lengths model S A start sizes)
  simpa only [List.length_map] using h

theorem range (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) :
    ∀ r ∈ (run model S A start sizes).1, start ≤ r.start ∧ r.stop ≤ start + sizes.sum := by
  induction sizes generalizing start with
  | nil => simp only [run,List.not_mem_nil,false_implies,implies_true]
  | cons size sizes ih =>
    intro r hr
    simp only [run,List.mem_cons] at hr
    rcases hr with rfl | hr
    · dsimp only [Region.stop]; simp only [List.sum_cons]; omega
    · obtain ⟨hl,hu⟩ := ih (start + size) r hr
      simp only [List.sum_cons]
      omega

theorem ordered (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) :
    List.Pairwise (fun r s : Region A => r.stop ≤ s.start) (run model S A start sizes).1 := by
  induction sizes generalizing start with
  | nil => exact List.Pairwise.nil
  | cons size sizes ih =>
    simp only [run]
    apply List.Pairwise.cons
    · intro r hr
      exact (range model S A (start + size) sizes r hr).1
    · exact ih _

theorem disjoint (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) :
    List.Pairwise (fun r s : Region A => Disjoint (Set.Ico r.start r.stop) (Set.Ico s.start s.stop))
      (run model S A start sizes).1 := by
  apply (ordered model S A start sizes).imp
  intro r s h
  apply Set.disjoint_left.mpr
  intro x hx hs
  simp only [Set.mem_Ico] at hx hs
  omega

theorem references (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ)
    (hCap : start + sizes.sum < 2 ^ A) :
    ∀ r ∈ (run model S A start sizes).1, r.reference.value = r.start := by
  induction sizes generalizing start with
  | nil => simp only [run,List.not_mem_nil,false_implies,implies_true]
  | cons size sizes ih =>
    intro r hr
    simp only [run,List.mem_cons] at hr
    rcases hr with rfl | hr
    · dsimp only
      rw [GeneralPaperStoredWordEncoding.word_data,FixedBinaryWord.value_ofNat]
      simp only [List.sum_cons] at hCap
      omega
    · exact ih (start + size) (by simp only [List.sum_cons] at hCap; omega) r hr

theorem reference_width (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ)
    (hA : 1 ≤ A) (hCap : start + sizes.sum < 2 ^ A) :
    ∀ r ∈ (run model S A start sizes).1, binaryWordWidth r.start ≤ A := by
  intro r hr
  have h := range model S A start sizes r hr
  exact binaryWordWidth_le_of_lt_pow hA (by unfold Region.stop at h; omega)

def stepPrice (model : RationalCostModel) (S A : ℕ) : ℕ :=
  A * GeneralPaperStoredWordEncoding.stepBound model S A A + 5 * model.rat (A + 1) +
    80 * S + 80 + 64 * (S + A + 1)

theorem work (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ)
    (hA : 1 ≤ A) (hCap : start + sizes.sum < 2 ^ A) :
    (run model S A start sizes).2.2 ≤ (sizes.length + 1) * stepPrice model S A := by
  induction sizes generalizing start with
  | nil => dsimp only [run,stepPrice,List.length_nil]; omega
  | cons size sizes ih =>
    have hTotal : start + size + sizes.sum < 2 ^ A := by simpa only [List.sum_cons,Nat.add_assoc] using hCap
    have hStart : binaryWordWidth start ≤ A := binaryWordWidth_le_of_lt_pow hA (by omega)
    have hSize : binaryWordWidth size ≤ A := binaryWordWidth_le_of_lt_pow hA (by omega)
    have hNext : binaryWordWidth (start + size) ≤ A := binaryWordWidth_le_of_lt_pow hA (by omega)
    have he := GeneralPaperStoredWordEncoding.work model S A start A hStart
    have hp := GeneralPaperEqualAddressConstruction.price_work model S start size (start + size) (A + 1)
      (by change 1 + binaryWordWidth start ≤ _; omega)
      (by change 1 + binaryWordWidth size ≤ _; omega)
      (by change 1 + binaryWordWidth (start + size) ≤ _; omega)
    have hi := ih (start + size) hTotal
    dsimp only [run,List.length_cons]
    unfold stepPrice at *
    nlinarith only [he,hp,hi]

end Blotto.GeneralPaperSequentialLayout
