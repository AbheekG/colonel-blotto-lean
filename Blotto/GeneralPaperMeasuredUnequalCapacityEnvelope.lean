import Blotto.GeneralPaperMeasuredUnequalCounterCapacity

/-! A capacity envelope from actual owned counter lengths. No numerical
time bound or repeated preparation pass is used to choose a reference. -/
namespace Blotto.GeneralPaperMeasuredUnequalCapacityEnvelope
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperEncodedScalarStorage (fields natBits)
open GeneralPaperMeasuredUnequalStorageFrame (initial child frame)
open GeneralPaperMeasuredUnequalStoragePhases (word word_eq)
open GeneralPaperMeasuredUnequalCounterCapacity
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def branch (model : RationalCostModel) (p : Problem) : ℕ :=
  GeneralPaperAllBranchBitDispatch.branchPrice model (GeneralPaperMeasuredReferenceGrowth.original p)

noncomputable def counterBound (model : RationalCostModel) (C d W K : ℕ) (p : Problem) : ℕ :=
  initProfile model W K p + GeneralPaperNativeResourceReferenceGrowth.reserve model C d W p +
    200 * W + natBits (branch model p)

theorem values_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    ∀ z ∈ GeneralPaperMeasuredUnequalStorageFrame.values model K p,
      natBits z ≤ counterBound model C d (cal.word p) K p := by
  have hw := word_eq cal K hWord p
  have hW : 1 ≤ word model K p := by rw [hw]; exact cal.positive p
  have hn := initial_field model K p hW p.n (by
    simp [GeneralPaperMixedInitializerControls.values, GeneralPaperOriginalGameInput.equalInput,
      GeneralPaperMeasuredReferenceGrowth.original])
  have hOne := initial_field model K p hW 1 (by simp [GeneralPaperMixedInitializerControls.values])
  have hK := initial_field model K p hW K (by simp [GeneralPaperMixedInitializerControls.values])
  have he := initial_return_field model K p hW (initial model K p).1.1.exponent (by simp)
  have hwBits := initial_return_field model K p hW (initial model K p).1.2 (by simp)
  have hi := initial_return_field model K p hW (initial model K p).2 (by simp)
  rw [hw] at hn hOne hK he hwBits hi
  have hc := child_work_bits hg cal K hWord p
  have hWrap : natBits (64 * (1 + (initial model K p).1.2 + 1)) ≤ 200 * cal.word p := by
    change natBits (64 * (1 + word model K p + 1)) ≤ _
    rw [hw]
    have h := GeneralPaperNaturalScalarLifetime.counter_word (64 * (1 + cal.word p + 1))
    have hp := cal.positive p
    change natBits _ ≤ _ at h
    omega
  have hSum := (bits_add (initial model K p).2 (child model K p).2).trans (Nat.add_le_add hi hc)
  have hTotal := (bits_add ((initial model K p).2 + (child model K p).2)
    (64 * (1 + (initial model K p).1.2 + 1))).trans (Nat.add_le_add hSum hWrap)
  have hLast := bits_add ((initial model K p).2 + (child model K p).2 + 64 * (1 + (initial model K p).1.2 + 1))
    (branch model p)
  intro z hz
  simp only [GeneralPaperMeasuredUnequalStorageFrame.values, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold counterBound branch
  dsimp only [branch] at hLast
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

noncomputable def envelope (model : RationalCostModel) (C d W K : ℕ) (p : Problem) : ℕ :=
  16384 * (initProfile model W K p + GeneralPaperNativeResourceReferenceGrowth.reserve model C d W p +
    W + natBits (branch model p) + 1)

theorem controls_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    fields (cal.word p) (GeneralPaperMeasuredUnequalStorageFrame.values model K p) + 384 * cal.word p ≤
      4096 * (initProfile model (cal.word p) K p +
        GeneralPaperNativeResourceReferenceGrowth.reserve model C d (cal.word p) p + cal.word p + natBits (branch model p)) := by
  have h := GeneralPaperEncodedScalarStorage.fields_bound (cal.word p) (counterBound model C d (cal.word p) K p)
    (GeneralPaperMeasuredUnequalStorageFrame.values model K p) (values_bound hg cal K hWord p)
  change fields (cal.word p) _ ≤ 12 * (counterBound model C d (cal.word p) K p + cal.word p) + 32 * cal.word p at h
  unfold counterBound at h
  omega

theorem frame_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    frame model K p ≤ 8192 * (initProfile model (cal.word p) K p +
      GeneralPaperNativeResourceReferenceGrowth.reserve model C d (cal.word p) p + cal.word p + natBits (branch model p)) := by
  have hi := GeneralPaperMixedInitializerPhases.all_phases model (cal.word p) 1 K (cal.positive p)
    (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) .returned
  have hc := controls_bound hg cal K hWord p
  dsimp only [GeneralPaperMixedInitializerPhases.window, GeneralPaperMixedInitializerPhases.component] at hi
  change _ ≤ initProfile model (cal.word p) K p at hi
  dsimp only [frame]
  change GeneralPaperEqualInputInitializerLifetime.inputOwner model (word model K p) _ +
    GeneralPaperMixedInitializerControls.returnedOwner model (word model K p) 1 K _ +
      fields (word model K p) _ + 384 * word model K p ≤ _
  rw [word_eq cal K hWord p]
  omega

theorem all_phases {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem)
    (phase : GeneralPaperMeasuredUnequalStoragePhases.Phase model K p) :
    GeneralPaperMeasuredUnequalStoragePhases.window model K p phase ≤ envelope model C d (cal.word p) K p := by
  have hw := word_eq cal K hWord p
  have hf := frame_bound hg cal K hWord p
  cases phase with
  | initialization phase =>
    have hi := GeneralPaperMixedInitializerPhases.all_phases model (cal.word p) 1 K (cal.positive p)
      (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) phase
    have hc := controls_bound hg cal K hWord p
    change _ ≤ initProfile model (cal.word p) K p at hi
    dsimp only [GeneralPaperMeasuredUnequalStoragePhases.window]
    rw [hw]
    unfold envelope
    omega
  | native source description =>
    have hn : ∀ (source : GeneralPaperClosedParsedStorage.SourceCursor model (word model K p)
          (GeneralPaperMeasuredUnequalStoragePhases.selected model K p) p.values p.selector p.correct)
        (description : GeneralPaperClosedParsedStorage.DescriptionCursor model (word model K p)
          (GeneralPaperMeasuredUnequalStoragePhases.selected model K p) p.values p.selector p.correct),
        GeneralPaperClosedParsedStorage.window model (word model K p)
          (GeneralPaperMeasuredUnequalStoragePhases.selected model K p) p.values p.selector p.correct
            p.budget p.budget_valid source description ≤
              GeneralPaperNativeResourceReferenceGrowth.reserve model C d (cal.word p) p := by
      dsimp only [GeneralPaperMeasuredUnequalStoragePhases.selected]
      rw [hw]
      exact GeneralPaperEnlargedReferenceSpace.parsed_window hg cal p
    have hs := hn source description
    dsimp only [GeneralPaperMeasuredUnequalStoragePhases.window]
    unfold envelope
    omega
  | returned =>
    have hr := GeneralPaperMeasuredUnequalStoragePhases.returned_bound hg cal K hWord p
    dsimp only [GeneralPaperMeasuredUnequalStoragePhases.window]
    rw [hw]
    unfold envelope
    omega

end Blotto.GeneralPaperMeasuredUnequalCapacityEnvelope
