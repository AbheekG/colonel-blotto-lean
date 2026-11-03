import Blotto.GeneralPaperAffineStepStorage

/-! Native score-zero initial affine table: partial/full buffers, literal
zero/empty witnesses, constructor stack and encoded native return fields. -/
namespace Blotto.GeneralPaperAffineInitialStorage
open RationalOrderCell GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
open GeneralPaperAffineWitnessStorage GeneralPaperAffinePickStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector GeneralPaperScoreConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def callback (W S K : ℕ) (s : Fin (S+1)) : Option (Choice K)×ℕ :=
  (if s.val=0 then some ⟨⟨0,0⟩,[]⟩ else none,32*W)

theorem callback_good (W S K : ℕ) (s : Fin (S+1)) : Good 0 1 (callback W S K s).1 := by
  intro c hc
  unfold callback at hc
  dsimp only at hc
  split at hc
  · cases hc
    exact ⟨by simp only [List.length_nil,le_refl],by norm_num [RationalHeight],by norm_num [RationalHeight]⟩
  · contradiction

def price (W S : ℕ) : ℕ := 120*(S+1)*W

def window (W S K count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) : ℕ :=
  reservedFootprint W (S+1) (optionChoiceFoot W)
      (PaperIndexedArrayConstruction.fill (fun w => w) W (callback W S K) count hc).1+
    constructorFrames (fun w => w) W W (callback W S K) count hc+optionChoiceFoot W (callback W S K s).1+
    fields W [S,K,count,s.val,(GeneralPaperParametricInitialPrice.run (fun w => w) W S K).2,32*W]+256*W

def profile (W S K : ℕ) : ℕ := tableProfile W S K 0 1+constructorProfile W (S+1) (price W S)+optionChoiceProfile W K 0 1+
  6*(natBits (S+K+1+price W S+32*W)+W)+288*W

theorem bounded (W S K : ℕ) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) : window W S K count hc s≤profile W S K := by
  have hPrefix := indexed_reserved_prefix (fun w => w) W W (optionChoiceProfile W K 0 1) (optionChoiceFoot W) (callback W S K)
    (fun s => option_choice_bound W 0 1 _ (callback_good W S K s)) count hc
  change reservedFootprint W (S+1) (optionChoiceFoot W)
    (PaperIndexedArrayConstruction.fill (fun w => w) W (callback W S K) count hc).1≤tableProfile W S K 0 1 at hPrefix
  have hWork := GeneralPaperParametricInitialPrice.bit_work W S K hW hIndex
  change (GeneralPaperParametricInitialPrice.run (fun w => w) W S K).2≤price W S at hWork
  have hConstructor := constructor_bound (fun w => w) W W (price W S) (callback W S K) hWork count hc
  have hCurrent := option_choice_bound W 0 1 _ (callback_good W S K s)
  have hs := s.isLt
  have hFields := fields_bound W (natBits (S+K+1+price W S+32*W))
    [S,K,count,s.val,(GeneralPaperParametricInitialPrice.run (fun w => w) W S K).2,32*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (S+K+1+price W S+32*W)+W)+32*W at hFields
  unfold window profile
  omega

end Blotto.GeneralPaperAffineInitialStorage
