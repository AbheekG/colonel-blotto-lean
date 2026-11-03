import Blotto.BinaryWholeObservationFrame
import Blotto.FareyNativeOutputCompiler

/-! The actual accepted temporal descriptor has a finite bit representation.
Readback restores both complete histories and the checked descriptor exactly,
including future draw semantics. The gate used in restoration remains the
existing semantic gate; representation does not prove efficient validation or
complete finite-binary arithmetic/metadata/space costs. -/

namespace Blotto.FareyTemporalOutput
open FareyUnitSourceInputs ProductSecurityTrainer BinaryWholeObservationFrame
open scoped Classical

def Prepared.encode {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) : List Bool :=
  encodeHistory p.richPast ++ encodeHistory p.poorPast

noncomputable def restore {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1))) : Option (Prepared ratio hr values epsilon he) :=
  if hRich : 0 < richPast.length ∧ richPast.length = (normalizedInput ratio hr values true).rounds epsilon then
    if hPoor : 0 < poorPast.length ∧ poorPast.length = (normalizedInput ratio hr values false).rounds epsilon then
      if hGate : temporalRationalGate ratio hr values epsilon he richPast poorPast hRich.1 hPoor.1 epsilon = true then
        some ⟨richPast,poorPast,hRich.1,hPoor.1,hRich.2,hPoor.2,hGate⟩
      else none
    else none
  else none

theorem restore_prepared {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) :
    restore ratio hr values epsilon he p.richPast p.poorPast = some p := by
  have hRich := And.intro p.rich_positive p.rich_length
  have hPoor := And.intro p.poor_positive p.poor_length
  unfold restore
  rw [dite_eq_left hRich, dite_eq_left hPoor, dite_eq_left p.gate]

noncomputable def readPrepared {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (bits : List Bool) :
    Option (Prepared ratio hr values epsilon he × List Bool) :=
  (readHistory (n + 1) bits).bind (fun rich =>
    (readHistory (n + 1) rich.2).bind (fun poor =>
      (restore ratio hr values epsilon he rich.1 poor.1).map (fun p => (p, poor.2))))

theorem Prepared.read_encode_append {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (suffix : List Bool) :
    readPrepared ratio hr values epsilon he (p.encode ++ suffix) = some (p, suffix) := by
  simp only [readPrepared, Prepared.encode, List.append_assoc, readHistory_encode_append,
    Option.bind_some, restore_prepared, Option.map_some]

theorem Prepared.encode_length {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) :
    p.encode.length =
      (2 * binaryWordWidth ((normalizedInput ratio hr values true).rounds epsilon) + 1 +
        (p.richPast.map (fun observed => (BinaryWholeObservationFrame.encode observed).length)).sum) +
      (2 * binaryWordWidth ((normalizedInput ratio hr values false).rounds epsilon) + 1 +
        (p.poorPast.map (fun observed => (BinaryWholeObservationFrame.encode observed).length)).sum) := by
  simp only [Prepared.encode, List.length_append, encodeHistory_length, p.rich_length, p.poor_length]

end Blotto.FareyTemporalOutput
