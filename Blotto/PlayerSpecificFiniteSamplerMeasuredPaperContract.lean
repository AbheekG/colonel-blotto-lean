import Blotto.PlayerSpecificFiniteSamplerMeasuredPreparationCost
import Blotto.PlayerSpecificFiniteSamplerNash

/-! The laws and continuous-game guarantees are attached to the same
measured public return whose preparation and draw source costs are bounded. -/
namespace Blotto.PlayerSpecificFiniteSamplerMeasuredPaperContract
open MeasureTheory PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def sample {N : ℕ} (p : Prepared N) (player : Bool)
    (bits : Fin (bitCount p) → Bool) : Allocation N :=
  PlayerSpecificRationalOutput.allocation
    (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).1

theorem sample_eq {N : ℕ} (p : Prepared N) (player : Bool)
    (bits : Fin (bitCount p) → Bool) :
    sample p player bits=PlayerSpecificFiniteSamplerLaw.sample p player bits := by
  simp only [sample,PlayerSpecificFiniteSamplerLaw.sample,
    PlayerSpecificFiniteSamplerMeasuredExecution.draw_value]

noncomputable def law {N : ℕ} (p : Prepared N) (player : Bool) : Mixed N :=
  (fairBitLaw (bitCount p)).map (sample p player)

theorem law_eq {N : ℕ} (p : Prepared N) (player : Bool) :
    law p player=PlayerSpecificFiniteSamplerLaw.law p player := by
  have hs : sample p player=PlayerSpecificFiniteSamplerLaw.sample p player := by
    funext bits
    exact sample_eq p player bits
  simp only [law,PlayerSpecificFiniteSamplerLaw.law,hs]

noncomputable def joint {N : ℕ} (p : Prepared N) : ProbabilityMeasure (Allocation N × Allocation N) :=
  (fairBitLaw (bitCount p+bitCount p)).map (fun bits =>
    (sample p true (firstBitBlock (bitCount p) (bitCount p) bits),
      sample p false (secondBitBlock (bitCount p) (bitCount p) bits)))

theorem joint_eq {N : ℕ} (p : Prepared N) :
    joint p=PlayerSpecificFiniteSamplerLaw.joint p := by
  have hsA : sample p true=PlayerSpecificFiniteSamplerLaw.sample p true := by
    funext bits
    exact sample_eq p true bits
  have hsB : sample p false=PlayerSpecificFiniteSamplerLaw.sample p false := by
    funext bits
    exact sample_eq p false bits
  simp only [joint,PlayerSpecificFiniteSamplerLaw.joint,hsA,hsB]

theorem accepted_contract {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2≤
        PlayerSpecificFiniteSamplerMeasuredPreparationCost.acceptedWork i epsilon p ∧
      (∀ (player : Bool) (bits : Fin (bitCount p) → Bool),
        (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).2≤
          PlayerSpecificRationalFiniteMeasuredSourceCost.work i
            p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits) ∧
      Supported 1 (law p true) ∧
      Supported (i.budget:ℝ) (law p false) ∧
      regret i.valuesA.values 1 (law p true) (law p false)≤(epsilon:ℝ) ∧
      regret i.valuesB.values (i.budget:ℝ) (law p false) (law p true)≤(epsilon:ℝ) ∧
      (joint p : Measure (Allocation N × Allocation N))=
        (law p true : Measure (Allocation N)).prod
          (law p false : Measure (Allocation N)) := by
  have hpublic : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [←PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  have hprepare:=PlayerSpecificFiniteSamplerMeasuredPreparationCost.accepted_cost i epsilon he p hp
  obtain ⟨x,hx,hdraw⟩:=PlayerSpecificFiniteSamplerMeasuredSourceJoin.accepted_draws i epsilon he p hp
  have hpaper:=PlayerSpecificFiniteSamplerNash.actual_contract i epsilon he p hpublic
  rw [law_eq,law_eq,joint_eq]
  exact ⟨hprepare,(fun player bits => (hdraw player bits).2.2),hpaper⟩

theorem all_continuous_deviations {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    (∀ y : Allocation N,Blotto.Feasible 1 y →
      purePayoff i.valuesA.values y (law p false)≤
        expected i.valuesA.values (law p true) (law p false)+(epsilon:ℝ)) ∧
    (∀ y : Allocation N,Blotto.Feasible (i.budget:ℝ) y →
      purePayoff i.valuesB.values y (law p true)≤
        expected i.valuesB.values (law p false) (law p true)+(epsilon:ℝ)) := by
  have hpublic : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [←PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  rw [law_eq,law_eq]
  exact PlayerSpecificFiniteSamplerNash.continuous_deviations i epsilon he p hpublic

end Blotto.PlayerSpecificFiniteSamplerMeasuredPaperContract
