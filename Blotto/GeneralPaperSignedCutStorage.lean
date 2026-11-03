import Blotto.GeneralPaperTagFamilyStorage

/-! The two signed-cut fills include their compulsory endpoint slot,
reserved buffers, scalar controls, native annotation and complete scratch.
No cut-code, capacity or metadata oracle is assumed. -/
namespace Blotto.GeneralPaperSignedCutStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSignedCutExecution
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem word (m U x : ℕ) (hx : x≤GeneralPaperSignedCutOperands.magnitude m U) :
    natBits x≤GeneralPaperSignedCutOperands.width m U :=
  (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans (GeneralPaperSignedCutOperands.word_bound m U)

theorem element_bound {m : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (hq : ∀ q,queries.read q≤U) (i : Fin (m+1)) :
    (element model.rat W U negative queries i).1≤2*U := by
  unfold element
  dsimp only
  split
  · rename_i hi
    have h := hq ⟨i.val,hi⟩
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  · cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

def filledPrefix {m : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (count : ℕ) (hc : count≤m+1) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W (m+1) natBits
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W (m+1))
      (element model.rat W U negative queries) count hc).1

theorem prefix_bound {m : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (hq : ∀ q,queries.read q≤U) (count : ℕ) (hc : count≤m+1) :
    filledPrefix model W U negative queries count hc≤(m+1)*(natBits (2*U)+W)+64*W := by
  apply GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w)
    (GeneralPaperSummaryArrayExecution.arrayWord W (m+1)) W (natBits (2*U)) natBits
    (element model.rat W U negative queries)
  intro i
  exact Nat.add_le_add_left (binaryWordWidth_mono (element_bound model W U negative queries hq i)) 1

def controls (W m _U count : ℕ) : ℕ := fields W [m,m+1,m+2,count,count+1,54*(m+1),54*(m+1)+18]

theorem controls_bound (W m U count : ℕ) (hc : count≤m+1) :
    controls W m U count≤7*(GeneralPaperSignedCutOperands.width m U+W)+32*W := by
  apply fields_bound
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx
  all_goals first | (cases hx; done) | (rw [hx]; apply word; unfold GeneralPaperSignedCutOperands.magnitude; omega)

def framePeak (W m U : ℕ) : ℕ := (m+2)*(7*(GeneralPaperSignedCutOperands.width m U+W)+160*W)

theorem frame_bound (W m U count : ℕ) (hc : count≤m+1) :
    controls W m U count+128*W≤7*(GeneralPaperSignedCutOperands.width m U+W)+160*W := by
  have h := controls_bound W m U count hc
  omega

def returned {m : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W (run true (fun w => w) model.rat W U negative queries).1.1+
    natBits (run true (fun w => w) model.rat W U negative queries).1.2+64*W

theorem returned_bound {m : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (hq : ∀ q,queries.read q≤U) :
    returned model W U negative queries≤(m+1)*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width m U+96*W := by
  have ha := GeneralPaperEncodedNatArray.bounded W (natBits (2*U))
    (run true (fun w => w) model.rat W U negative queries).1.1 (fun i =>
      Nat.add_le_add_left (binaryWordWidth_mono (GeneralPaperSignedCutPrice.codes true (fun w => w) model.rat W U negative queries hq i)) 1)
  have hw := word m U (54*(m+1)+18) (by unfold GeneralPaperSignedCutOperands.magnitude; omega)
  change natBits (run true (fun w => w) model.rat W U negative queries).1.2≤_ at hw
  unfold returned
  omega

def window {m : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ)
    (count : ℕ) (hc : count≤m+1) (i : Fin (m+1)) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W queries+2*filledPrefix model W U negative queries count hc+
    framePeak W m U+controls W m U count+returned model W U negative queries+
    natBits (element model.rat W U negative queries i).1+
    (run true (fun w => w) model.rat W U negative queries).2+256*W

def profile (model : RationalCostModel) (W m U : ℕ) : ℕ :=
  (m*(natBits U+W)+32*W)+2*((m+1)*(natBits (2*U)+W)+64*W)+framePeak W m U+
    (7*(GeneralPaperSignedCutOperands.width m U+W)+32*W)+
    ((m+1)*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width m U+96*W)+natBits (2*U)+
    GeneralPaperSignedCutPrice.profile model.rat W m U+256*W

theorem bounded {m : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ)
    (hq : ∀ q,queries.read q≤U) (count : ℕ) (hc : count≤m+1) (i : Fin (m+1)) :
    window model W U negative queries count hc i≤profile model W m U := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits U) queries (fun q => Nat.add_le_add_left (binaryWordWidth_mono (hq q)) 1)
  have hp := prefix_bound model W U negative queries hq count hc
  have hs := controls_bound W m U count hc
  have hr := returned_bound model W U negative queries hq
  have he := Nat.add_le_add_left (binaryWordWidth_mono (element_bound model W U negative queries hq i)) 1
  change natBits (element model.rat W U negative queries i).1≤natBits (2*U) at he
  have hw := GeneralPaperSignedCutPrice.bit_work model.rat model.monotone W U negative queries hq
  unfold window profile
  omega

end Blotto.GeneralPaperSignedCutStorage
