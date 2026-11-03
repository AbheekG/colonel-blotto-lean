import Blotto.FareyCertifiedSourceRestart
import Blotto.FairBitFirstSuccessMap
import Blotto.CompactTemporalSamplerLaw

/-! Accepted source output retains both actual finite rational histories,
with proof-erased positivity/gate certificates. The laws are derived from
those histories. Flat-source and bounded restart erasure give exactly the
previous certified law outputs and rejection events. This is a strategy
descriptor; efficient gate access and physical encoding/prices remain separate. -/

namespace Blotto.FareyTemporalOutput
open FareyUnitSourceInputs FareySourceTraining ProductSecurityTrainer
open scoped BigOperators Classical

structure Prepared {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) where
  richPast : List (RawObservation (n + 1))
  poorPast : List (RawObservation (n + 1))
  rich_positive : 0 < richPast.length
  poor_positive : 0 < poorPast.length
  rich_length : richPast.length = (normalizedInput ratio hr values true).rounds epsilon
  poor_length : poorPast.length = (normalizedInput ratio hr values false).rounds epsilon
  gate : temporalRationalGate ratio hr values epsilon he richPast poorPast rich_positive poor_positive epsilon = true

noncomputable def Prepared.laws {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) : Mixed (n + 1) × Mixed (n + 1) :=
  (((trainer ratio hr values true epsilon he).averageLawA p.richPast p.rich_positive).law,
    ((trainer ratio hr values false epsilon he).averageLawA p.poorPast p.poor_positive).law)

theorem Prepared.laws_sound {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) :
    Supported 1 p.laws.1 ∧ Supported (ratio : ℝ) p.laws.2 ∧
      regret values.values 1 p.laws.1 p.laws.2 ≤ (epsilon : ℝ) ∧
        regret values.values (ratio : ℝ) p.laws.2 p.laws.1 ≤ (epsilon : ℝ) :=
  ⟨rich_temporal_supported ratio hr values epsilon he p.richPast p.rich_positive,
    poor_temporal_supported ratio hr values epsilon he p.poorPast p.poor_positive,
    temporalRationalGate_sound ratio hr values epsilon he p.richPast p.poorPast
      p.rich_positive p.poor_positive epsilon p.gate⟩

noncomputable def prepare {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (richBits : Fin ((normalizedInput ratio hr values true).rounds epsilon *
      (normalizedInput ratio hr values true).seedCap epsilon he accuracy) → Bool)
    (poorBits : Fin ((normalizedInput ratio hr values false).rounds epsilon *
      (normalizedInput ratio hr values false).seedCap epsilon he accuracy) → Bool) :
    Option (Prepared ratio hr values epsilon he) :=
  let richPast := (normalizedInput ratio hr values true).run epsilon he accuracy richBits
  let poorPast := (normalizedInput ratio hr values false).run epsilon he accuracy poorBits
  let richPositive := source_run_positive _ epsilon he accuracy richBits
  let poorPositive := source_run_positive _ epsilon he accuracy poorBits
  if hGate : temporalRationalGate ratio hr values epsilon he richPast poorPast richPositive poorPositive epsilon = true then
    some ⟨richPast,poorPast,richPositive,poorPositive,
      source_run_length _ epsilon he accuracy richBits,
      source_run_length _ epsilon he accuracy poorBits,hGate⟩
  else none

theorem prepare_laws {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (richBits : Fin ((normalizedInput ratio hr values true).rounds epsilon *
      (normalizedInput ratio hr values true).seedCap epsilon he accuracy) → Bool)
    (poorBits : Fin ((normalizedInput ratio hr values false).rounds epsilon *
      (normalizedInput ratio hr values false).seedCap epsilon he accuracy) → Bool) :
    (prepare ratio hr values epsilon he accuracy richBits poorBits).map Prepared.laws =
      certifiedSourceRun ratio hr values epsilon he accuracy epsilon richBits poorBits := by
  unfold prepare certifiedSourceRun
  dsimp only
  split
  · simp_all only [Option.map_some, Prepared.laws]
  · simp_all only [Option.map_none]

noncomputable def prepareFlat {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (sourceSeedCap ratio hr values epsilon he accuracy) → Bool) :
    Option (Prepared ratio hr values epsilon he) :=
  let R := (normalizedInput ratio hr values true).rounds epsilon *
    (normalizedInput ratio hr values true).seedCap epsilon he accuracy
  let P := (normalizedInput ratio hr values false).rounds epsilon *
    (normalizedInput ratio hr values false).seedCap epsilon he accuracy
  prepare ratio hr values epsilon he accuracy (firstBitBlock R P bits) (secondBitBlock R P bits)

theorem prepareFlat_laws {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (sourceSeedCap ratio hr values epsilon he accuracy) → Bool) :
    (prepareFlat ratio hr values epsilon he accuracy bits).map Prepared.laws =
      certifiedFlatSourceRun ratio hr values epsilon he accuracy bits :=
  prepare_laws ratio hr values epsilon he accuracy _ _

noncomputable def restart {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * sourceSeedCap ratio hr values epsilon he accuracy) → Bool) :
    Option (Prepared ratio hr values epsilon he) :=
  FairBitFirstSuccess.run (sourceSeedCap ratio hr values epsilon he accuracy)
    (prepareFlat ratio hr values epsilon he accuracy) attempts bits

theorem restart_laws {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * sourceSeedCap ratio hr values epsilon he accuracy) → Bool) :
    (restart ratio hr values epsilon he accuracy attempts bits).map Prepared.laws =
      certifiedSourceRestart ratio hr values epsilon he accuracy attempts bits := by
  unfold restart certifiedSourceRestart
  rw [← FairBitFirstSuccess.run_map]
  have hTrial : (fun seed => (prepareFlat ratio hr values epsilon he accuracy seed).map Prepared.laws) =
      certifiedFlatSourceRun ratio hr values epsilon he accuracy := by
    funext seed
    exact prepareFlat_laws ratio hr values epsilon he accuracy seed
  rw [hTrial]

theorem restart_failure_bound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1) (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) (attempts : ℕ) :
    (fairBitKernel (attempts * sourceSeedCap ratio hr values epsilon he accuracy)).mean (fun bits =>
      if restart ratio hr values epsilon he accuracy attempts bits = none then 1 else 0) ≤ (1 / 4 : ℝ) ^ attempts := by
  have hNone : ∀ bits, restart ratio hr values epsilon he accuracy attempts bits = none ↔
      certifiedSourceRestart ratio hr values epsilon he accuracy attempts bits = none := by
    intro bits
    rw [← restart_laws]
    cases restart ratio hr values epsilon he accuracy attempts bits <;> simp
  simp_rw [hNone]
  exact source_restart_failure_bound ratio hr values epsilon he accuracy ha attempts

end Blotto.FareyTemporalOutput
