import Blotto.GeneralPaperLeastValid

/-! Inclusive-interval lookup contracts, including exact absence, reversed
intervals, zero, and invalid tail codes. All witnesses are actual decoder
outputs; the mathematical validity predicate is equivalent to execution.
-/
namespace Blotto.GeneralPaperLeastValidSpec
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeDecodeSound
open GeneralPaperCodeMinimumScan GeneralPaperLeastValid
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2048

theorem run_sound (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry)
    (hSome : (run a response lo hi).selected=some entry) : Possible a response lo hi entry := by
  have hb := run_best a response lo hi
  rw [hSome] at hb
  exact hb.1

theorem run_minimal (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry)
    (hSome : (run a response lo hi).selected=some entry) (code : ℕ)
    (hLo : lo≤code) (hHi : code≤hi) (hValid : Valid a response code) : entry.cost≤code := by
  obtain ⟨choice,hDecode⟩ := (GeneralPaperCodeDecodeComplete.valid_iff_decode a response code).mp hValid
  have hb := run_best a response lo hi
  rw [hSome] at hb
  exact hb.2 ⟨code,choice⟩ ⟨hLo,hHi,hDecode⟩

theorem run_some_iff (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (∃ entry, (run a response lo hi).selected=some entry) ↔ ∃ code, lo≤code ∧ code≤hi ∧ Valid a response code := by
  constructor
  · rintro ⟨entry,hSome⟩
    have hs := run_sound a response lo hi entry hSome
    exact ⟨entry.cost,hs.1,hs.2.1,decode_valid a response entry.cost entry.predecessor hs.2.2⟩
  · rintro ⟨code,hLo,hHi,hValid⟩
    obtain ⟨choice,hDecode⟩ := (GeneralPaperCodeDecodeComplete.valid_iff_decode a response code).mp hValid
    cases he : (run a response lo hi).selected with
    | none =>
      have hb := run_best a response lo hi
      rw [he] at hb
      exact (hb ⟨code,choice⟩ ⟨hLo,hHi,hDecode⟩).elim
    | some entry => exact ⟨entry,rfl⟩

theorem run_none_iff (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run a response lo hi).selected=none ↔ ∀ code, lo≤code → code≤hi → ¬Valid a response code := by
  constructor
  · intro hNone code hLo hHi hValid
    obtain ⟨entry,hSome⟩ := (run_some_iff a response lo hi).mpr ⟨code,hLo,hHi,hValid⟩
    rw [hNone] at hSome
    cases hSome
  · intro hEmpty
    cases he : (run a response lo hi).selected with
    | none => rfl
    | some entry =>
      obtain ⟨code,hLo,hHi,hValid⟩ := (run_some_iff a response lo hi).mp ⟨entry,he⟩
      exact (hEmpty code hLo hHi hValid).elim

theorem reversed_none (a : Alphabet) (response : Bool) (lo hi : ℕ) (hRange : hi<lo) :
    (run a response lo hi).selected=none := by
  apply (run_none_iff a response lo hi).mpr
  intro code hLo hHi _
  omega

theorem tail_none (a : Alphabet) (response : Bool) (lo hi : ℕ) (hTail : 4*a.C<lo) :
    (run a response lo hi).selected=none := by
  apply (run_none_iff a response lo hi).mpr
  intro code hLo _ hValid
  have he := valid_code_bound a response code hValid
  omega

theorem decoded_denominator (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry)
    (hSome : (run a response lo hi).selected=some entry) : entry.predecessor.threshold.den≤a.C :=
  (decode_sound a response entry.cost entry.predecessor (run_sound a response lo hi entry hSome).2.2).2

theorem candidate_closed (a : Alphabet) (lo hi : ℕ) (entry : Entry)
    (hSome : (run a false lo hi).selected=some entry) : entry.predecessor.opened=false :=
  GeneralPaperCodeDecodeSound.candidate_closed a entry.cost entry.predecessor (run_sound a false lo hi entry hSome).2.2

theorem run_zero (a : Alphabet) (response : Bool) (hi : ℕ) :
    (run a response 0 hi).selected=some ⟨0,⟨grid a 0,false⟩⟩ := by
  obtain ⟨entry,hSome⟩ := (run_some_iff a response 0 hi).mpr
    ⟨0,le_rfl,Nat.zero_le _,by simpa only [Nat.mul_zero] using valid_grid a response 0 (Nat.zero_le _)⟩
  have hCost := run_minimal a response 0 hi entry hSome 0 le_rfl (Nat.zero_le _)
    (by simpa only [Nat.mul_zero] using valid_grid a response 0 (Nat.zero_le _))
  have hz : entry.cost=0 := Nat.eq_zero_of_le_zero hCost
  have hDecode := (run_sound a response 0 hi entry hSome).2.2
  rw [hz,decode_zero] at hDecode
  have hChoice := Option.some.inj hDecode
  have he : entry=(⟨0,⟨grid a 0,false⟩⟩:Entry) := by
    cases entry with
    | mk cost choice =>
      dsimp only at hz hChoice ⊢
      cases hz
      cases hChoice
      rfl
  exact hSome.trans (congrArg some he)

end Blotto.GeneralPaperLeastValidSpec
