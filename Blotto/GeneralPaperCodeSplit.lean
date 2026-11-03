import Blotto.GeneralPaperCodeAlphabet

/-! Split a constructed code into bucket and one of four slots by the
arithmetic quotient routine. Primitive division/modulus occur only in the
specification. The cached alphabet exponent supplies the constructed cap.
-/
namespace Blotto.GeneralPaperCodeSplit
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  bucket : ℕ
  slot : ℕ
  work : ℕ

def run (code lambda : ℕ) : Result :=
  let divided := GeneralPaperConstructedNatDivision.run code 4 (lambda+1)
  ⟨divided.quotient,divided.remainder,divided.work+12⟩

theorem cap (a : Alphabet) (code : ℕ) (hCode : code≤4*a.C) : code<4*2^(a.lambda+1) := by
  have hc := a.scalePositive
  have hp := a.dyadic
  rw [pow_succ]
  omega

theorem run_spec (a : Alphabet) (code : ℕ) (hCode : code≤4*a.C) :
    code=4*(run code a.lambda).bucket+(run code a.lambda).slot ∧ (run code a.lambda).slot<4 :=
  GeneralPaperConstructedNatDivision.run_spec code 4 (a.lambda+1) (by decide) (cap a code hCode)

theorem run_pack (a : Alphabet) (t slot : ℕ) (hSlot : slot<4) (hCode : 4*t+slot≤4*a.C) :
    (run (4*t+slot) a.lambda).bucket=t ∧ (run (4*t+slot) a.lambda).slot=slot := by
  have he := run_spec a (4*t+slot) hCode
  omega

theorem run_work (code lambda : ℕ) : (run code lambda).work≤14*lambda+42 := by
  have he := GeneralPaperConstructedNatDivision.work_depth code 4 (lambda+1)
  have hd := GeneralPaperConstructedNatDivision.depth_le_fuel code 4 (lambda+1)
  dsimp only [run]
  omega

end Blotto.GeneralPaperCodeSplit
