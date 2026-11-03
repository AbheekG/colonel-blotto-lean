import Blotto.BinaryRatFrameDecodingCost
import Blotto.BinaryRatListFrame

/-! The sequence reader's actual short-circuit structure has work bounded
by the frame length even when a malformed input declares an enormous count.
Every successful rational frame consumes at least one bit. This is a labelled
primitive/cell work bound; physical record/allocation/addressing is separate. -/

namespace Blotto.BinaryRatListFrame

def decodingBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) : ℕ → List Bool → ℕ
  | 0, _ => 1
  | count + 1, frame =>
    BinaryRatFrame.decodingBitWork model primitive frame + 1 +
      match BinaryRatFrame.read frame with
      | none => 0
      | some first => decodingBitWork model primitive count first.2

def decodingFramePrice (model : RationalCostModel) (c length : ℕ) : ℕ :=
  (10 * c + 30) * (length + 2) ^ 2 + 5 * model.rat (4 * length + 13)

theorem decodingFramePrice_mono (model : RationalCostModel) (c : ℕ) :
    Monotone (decodingFramePrice model c) := by
  intro a b hab
  unfold decodingFramePrice
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hab _) _))
    (Nat.mul_le_mul_left _ (model.monotone (by omega)))

theorem decodingBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (frame : List Bool) :
    decodingBitWork model primitive count frame ≤
      (frame.length + 1) * (decodingFramePrice model c frame.length + 1) := by
  induction count generalizing frame with
  | zero =>
    simp only [decodingBitWork]
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))
  | succ count ih =>
    have hHead := BinaryRatFrame.decodingBitWork_bound model primitive c hPrimitive frame
    change BinaryRatFrame.decodingBitWork model primitive frame ≤ decodingFramePrice model c frame.length at hHead
    simp only [decodingBitWork]
    cases hRead : BinaryRatFrame.read frame with
    | none =>
      simp only
      have hMul := Nat.mul_le_mul_right (decodingFramePrice model c frame.length + 1)
        (show 1 ≤ frame.length + 1 by omega)
      simp only [Nat.one_mul] at hMul
      omega
    | some first =>
      rcases first with ⟨q, suffix⟩
      have hSuffix := BinaryRatFrame.read_suffix_lt frame q suffix hRead
      have hRest := (ih suffix).trans (Nat.mul_le_mul_left (suffix.length + 1)
        (Nat.add_le_add_right (decodingFramePrice_mono model c hSuffix.le) 1))
      simp only
      have hMul := Nat.mul_le_mul_right (decodingFramePrice model c frame.length + 1)
        (show suffix.length + 2 ≤ frame.length + 1 by omega)
      nlinarith

theorem read_suffix_length (count : ℕ) (frame : List Bool) (values : List ℚ) (suffix : List Bool)
    (h : read count frame = some (values, suffix)) : suffix.length ≤ frame.length := by
  induction count generalizing frame values suffix with
  | zero => cases Option.some.inj h; exact le_rfl
  | succ count ih =>
    simp only [read] at h
    cases hFirst : BinaryRatFrame.read frame with
    | none => rw [hFirst, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨q, tail⟩
      rw [hFirst, Option.bind_some] at h
      cases hRest : read count tail with
      | none => rw [hRest, Option.map_none] at h; cases h
      | some rest =>
        rcases rest with ⟨row, remaining⟩
        rw [hRest, Option.map_some] at h
        cases Option.some.inj h
        exact (ih tail row remaining hRest).trans (BinaryRatFrame.read_suffix_length frame q tail hFirst)

theorem read_count_and_consumption (count : ℕ) (frame : List Bool) (values : List ℚ) (suffix : List Bool)
    (h : read count frame = some (values, suffix)) :
    values.length = count ∧ count + suffix.length ≤ frame.length := by
  induction count generalizing frame values suffix with
  | zero => cases Option.some.inj h; simp
  | succ count ih =>
    simp only [read] at h
    cases hFirst : BinaryRatFrame.read frame with
    | none => rw [hFirst, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨q, tail⟩
      rw [hFirst, Option.bind_some] at h
      cases hRest : read count tail with
      | none => rw [hRest, Option.map_none] at h; cases h
      | some rest =>
        rcases rest with ⟨row, remaining⟩
        rw [hRest, Option.map_some] at h
        cases Option.some.inj h
        have hr := ih tail row remaining hRest
        have ht := BinaryRatFrame.read_suffix_lt frame q tail hFirst
        simp only [List.length_cons]
        constructor <;> omega

end Blotto.BinaryRatListFrame
