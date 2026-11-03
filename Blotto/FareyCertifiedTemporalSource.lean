import Blotto.FareyTemporalRationalGate

/-! The two actual bounded-bit source runs now feed their exact rational
security gate and return both temporal whole-allocation laws on acceptance.
Every accepted pair has canonical continuous regret bounds and independent
product play. Rejection is explicit. This semantic output composition proves
neither efficient temporal/extrema access nor a positive acceptance probability;
the general minimax/comparator, original-game compiler and model-cost chains
remain required. Preparation randomness selects a pair of laws; the players
then sample those fixed laws independently, without sharing a draw seed. -/

namespace Blotto.FareyUnitSourceInputs
open FareySourceTraining ProductSecurityTrainer
open scoped BigOperators Classical

noncomputable def certifiedSourceRun {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy tolerance : ℚ)
    (richBits : Fin ((normalizedInput ratio hr values true).rounds epsilon *
      (normalizedInput ratio hr values true).seedCap epsilon he accuracy) → Bool)
    (poorBits : Fin ((normalizedInput ratio hr values false).rounds epsilon *
      (normalizedInput ratio hr values false).seedCap epsilon he accuracy) → Bool) :
    Option (Mixed (n + 1) × Mixed (n + 1)) :=
  let richInput := normalizedInput ratio hr values true
  let poorInput := normalizedInput ratio hr values false
  let richPast := richInput.run epsilon he accuracy richBits
  let poorPast := poorInput.run epsilon he accuracy poorBits
  let hRich := source_run_positive richInput epsilon he accuracy richBits
  let hPoor := source_run_positive poorInput epsilon he accuracy poorBits
  if temporalRationalGate ratio hr values epsilon he richPast poorPast hRich hPoor tolerance then
    some (((trainer ratio hr values true epsilon he).averageLawA richPast hRich).law,
      ((trainer ratio hr values false epsilon he).averageLawA poorPast hPoor).law)
  else none

theorem certifiedSourceRun_sound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy tolerance : ℚ)
    (richBits : Fin ((normalizedInput ratio hr values true).rounds epsilon *
      (normalizedInput ratio hr values true).seedCap epsilon he accuracy) → Bool)
    (poorBits : Fin ((normalizedInput ratio hr values false).rounds epsilon *
      (normalizedInput ratio hr values false).seedCap epsilon he accuracy) → Bool)
    (richLaw poorLaw : Mixed (n + 1))
    (hResult : certifiedSourceRun ratio hr values epsilon he accuracy tolerance
      richBits poorBits = some (richLaw, poorLaw)) :
    Supported 1 richLaw ∧ Supported (ratio : ℝ) poorLaw ∧
      regret values.values 1 richLaw poorLaw ≤ (tolerance : ℝ) ∧
        regret values.values (ratio : ℝ) poorLaw richLaw ≤ (tolerance : ℝ) := by
  let richInput := normalizedInput ratio hr values true
  let poorInput := normalizedInput ratio hr values false
  let richPast := richInput.run epsilon he accuracy richBits
  let poorPast := poorInput.run epsilon he accuracy poorBits
  let hRich := source_run_positive richInput epsilon he accuracy richBits
  let hPoor := source_run_positive poorInput epsilon he accuracy poorBits
  change (if temporalRationalGate ratio hr values epsilon he richPast poorPast hRich hPoor tolerance then
    some (((trainer ratio hr values true epsilon he).averageLawA richPast hRich).law,
      ((trainer ratio hr values false epsilon he).averageLawA poorPast hPoor).law)
    else none) = some (richLaw, poorLaw) at hResult
  split at hResult
  next hGate =>
    have hPair := Option.some.inj hResult
    have hRichLaw := congrArg Prod.fst hPair
    have hPoorLaw := congrArg Prod.snd hPair
    dsimp only at hRichLaw hPoorLaw
    rw [← hRichLaw, ← hPoorLaw]
    exact ⟨rich_temporal_supported ratio hr values epsilon he richPast hRich,
      poor_temporal_supported ratio hr values epsilon he poorPast hPoor,
      temporalRationalGate_sound ratio hr values epsilon he richPast poorPast hRich hPoor tolerance hGate⟩
  next _ => cases hResult

theorem certifiedSourceRun_security_sum {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy tolerance : ℚ)
    (richBits : Fin ((normalizedInput ratio hr values true).rounds epsilon *
      (normalizedInput ratio hr values true).seedCap epsilon he accuracy) → Bool)
    (poorBits : Fin ((normalizedInput ratio hr values false).rounds epsilon *
      (normalizedInput ratio hr values false).seedCap epsilon he accuracy) → Bool)
    (richLaw poorLaw : Mixed (n + 1))
    (hResult : certifiedSourceRun ratio hr values epsilon he accuracy tolerance
      richBits poorBits = some (richLaw, poorLaw)) :
    security values.values 1 poorLaw + security values.values (ratio : ℝ) richLaw ≤
      1 + (tolerance : ℝ) := by
  let richInput := normalizedInput ratio hr values true
  let poorInput := normalizedInput ratio hr values false
  let richPast := richInput.run epsilon he accuracy richBits
  let poorPast := poorInput.run epsilon he accuracy poorBits
  let hRich := source_run_positive richInput epsilon he accuracy richBits
  let hPoor := source_run_positive poorInput epsilon he accuracy poorBits
  change (if temporalRationalGate ratio hr values epsilon he richPast poorPast hRich hPoor tolerance then
    some (((trainer ratio hr values true epsilon he).averageLawA richPast hRich).law,
      ((trainer ratio hr values false epsilon he).averageLawA poorPast hPoor).law)
    else none) = some (richLaw, poorLaw) at hResult
  split at hResult
  next hGate =>
    have hPair := Option.some.inj hResult
    have hRichLaw := congrArg Prod.fst hPair
    have hPoorLaw := congrArg Prod.snd hPair
    dsimp only at hRichLaw hPoorLaw
    rw [← hRichLaw, ← hPoorLaw, poor_temporal_security, rich_temporal_security]
    have hSum := (temporalRationalGate_true_iff ratio hr values epsilon he
      richPast poorPast hRich hPoor tolerance).1 hGate
    have hPairGate := temporal_pair_gate_iff ratio hr values epsilon he richPast poorPast
      hRich hPoor (tolerance : ℝ)
    have hExact := hPairGate.mpr hSum
    linarith
  next _ => cases hResult

end Blotto.FareyUnitSourceInputs
