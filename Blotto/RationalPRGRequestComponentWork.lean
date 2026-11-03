import Blotto.RationalPRGRequestPackingCopyWork

/-! A common request gate lifts sampler work components to the retained
parse/suffix/seed interface. Its bound covers every supplied bit path and its
failure theorem follows actual request execution. Parser costs are separate. -/

namespace Blotto.RationalPRGBinaryRequest

abbrev SamplerWorkComponent := ∀ {n : ℕ}, RationalPRGOriginalInput n → (K : ℕ) →
  (Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) → ℕ

noncomputable def acceptedComponentWork (component : SamplerWorkComponent) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => component parsed.1.2 K table.read
    else 0

theorem acceptedComponentWork_bound (component : SamplerWorkComponent) (frame seed : List Bool) (bound : ℕ)
    (hComponent : ∀ (input : Σ n, RationalPRGOriginalInput n) (words : BinaryAccuracyWords) (suffix : List Bool),
      readWords frame = some (input, words, suffix) →
        ∀ bits : Fin (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) → Bool,
          component input.2 words.precision bits ≤ bound) :
    acceptedComponentWork component frame seed ≤ bound := by
  unfold acceptedComponentWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table => exact hComponent input words suffix hParsed table.read
    · exact Nat.zero_le _

theorem acceptedComponentWork_incoming_bound (component : SamplerWorkComponent) (frame seed : List Bool) (bound : ℕ)
    (hComponent : ∀ (input : Σ n, RationalPRGOriginalInput n) (K : ℕ)
      (bits : Fin (RationalLottoResourceSystem.sampleBitBudget input.1 K) → Bool),
      input.1 ≤ frame.length → input.2.originalInputWordWidth ≤ (frame.length + 2) * (4 * frame.length + 13) →
        K ≤ frame.length + 6 → component input.2 K bits ≤ bound) :
    acceptedComponentWork component frame seed ≤ bound := by
  apply acceptedComponentWork_bound component frame seed bound
  intro input words suffix hParsed bits
  have hSize := readWords_bounds frame input words suffix hParsed
  exact hComponent input words.precision bits hSize.1
    (readWords_inputWordWidth frame input words suffix hParsed) hSize.2.2

theorem acceptedComponentWork_run_failure (component : SamplerWorkComponent) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : acceptedComponentWork component frame seed = 0 := by
  unfold run at h
  unfold acceptedComponentWork
  cases hParsed : readWords frame with
  | none => rfl
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    rw [hParsed, Option.bind_some] at h
    dsimp only at h ⊢
    split at h
    · rename_i hSuffix
      rw [ite_eq_left hSuffix]
      cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => rfl
      | some table => rw [hSeed, Option.map_some] at h; cases h
    · rename_i hSuffix
      rw [ite_eq_right hSuffix]

end Blotto.RationalPRGBinaryRequest
