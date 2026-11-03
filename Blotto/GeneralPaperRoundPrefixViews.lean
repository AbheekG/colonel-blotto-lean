import Blotto.GeneralPaperActualNativeProfitFields

/-! Two indexed reference-array views expose the pre-update signed-block
prefixes to candidate/response row selection. Prefix payloads are borrowed,
not copied or rebuilt. All reads, writes, indices and descriptors count.
-/
namespace Blotto.GeneralPaperRoundPrefixViews
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperEpochSnapshot
open GeneralPaperCatalogueOccurrenceHistory (Learner block)
open GeneralPaperCatalogueEpochRun
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def family {m k : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (learner : Learner)
    (before : FixedArrayTable m (Snapshot k)) : FixedArrayTable m (Prefix k) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (fun j => ((block learner (before.read j)).cdf,64*W))

def run {m k : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (before : FixedArrayTable m (Snapshot k)) :
    (FixedArrayTable m (Prefix k) × FixedArrayTable m (Prefix k)) × ℕ :=
  let candidate := family bits index W .lambda before
  let response := family bits index W .mu before
  ((candidate.1,response.1),candidate.2+response.2+64*W)

def familyProfile (W m : ℕ) : ℕ := m*(64*W)+44*(m+1)*arrayWord W m
def profile (W m : ℕ) : ℕ := 2*familyProfile W m+64*W
def arithmeticFamilyProfile (m : ℕ) : ℕ := m*64+44*(m+1)
def arithmeticProfile (m : ℕ) : ℕ := 2*arithmeticFamilyProfile m+64

theorem family_data {m k : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (learner : Learner)
    (before : FixedArrayTable m (Snapshot k)) :
    (family bits index W learner before).1=FixedArrayTable.ofFn (fun j => (block learner (before.read j)).cdf) :=
  PaperIndexedArrayConstruction.run_data index _ _

theorem data {m k : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (before : FixedArrayTable m (Snapshot k)) :
    (run bits index W before).1=
      (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf),FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) := by
  unfold run
  dsimp only
  rw [family_data,family_data]
  rfl

theorem family_bit_work {m k : ℕ} (W : ℕ) (learner : Learner) (before : FixedArrayTable m (Snapshot k)) :
    (family true (fun w => w) W learner before).2≤familyProfile W m :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) _
    (fun j => ((block learner (before.read j)).cdf,64*W))
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m) (fun _ => Nat.le_refl _)

theorem family_arithmetic_work {m k : ℕ} (learner : Learner) (before : FixedArrayTable m (Snapshot k)) :
    (family false (fun _ => 1) 1 learner before).2≤arithmeticFamilyProfile m := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 64
    (fun j => ((block learner (before.read j)).cdf,64)) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  simpa only [family,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticFamilyProfile] using h

theorem bit_work {m k : ℕ} (W : ℕ) (before : FixedArrayTable m (Snapshot k)) :
    (run true (fun w => w) W before).2≤profile W m := by
  have h := Nat.add_le_add_right (Nat.add_le_add (family_bit_work W .lambda before) (family_bit_work W .mu before)) (64*W)
  exact h.trans_eq (by unfold profile; ring)

theorem arithmetic_work {m k : ℕ} (before : FixedArrayTable m (Snapshot k)) :
    (run false (fun _ => 1) 1 before).2≤arithmeticProfile m := by
  have h := Nat.add_le_add_right (Nat.add_le_add (family_arithmetic_work .lambda before) (family_arithmetic_work .mu before)) 64
  exact h.trans_eq (by unfold arithmeticProfile; ring)

theorem same_data {m k : ℕ} (W : ℕ) (before : FixedArrayTable m (Snapshot k)) :
    (run true (fun w => w) W before).1=(run false (fun _ => 1) 1 before).1 := by rw [data,data]

theorem selected_good {m k : ℕ} (bits : Bool) (index : ℕ → ℕ) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let before := beforeAt (selected cache Qv weights Bc Br) time
    GeneralPaperMeshPrefixInvariant.Good m cache.alphabet.lambda k Qv ((run bits index W before).1.1.read j) ∧
    GeneralPaperMeshPrefixInvariant.Good m cache.alphabet.lambda k Qv ((run bits index W before).1.2.read j) := by
  dsimp only
  rw [data,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  exact ⟨GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda,
    GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu⟩

end Blotto.GeneralPaperRoundPrefixViews
