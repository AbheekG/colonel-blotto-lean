import Blotto.PlayerSpecificRealSampler

/-! The original rational-input augmented-real-RAM entry: recognize, retain
one passing pair, prepare the three arrays once, and sample either player's
whole allocation. Rejection is exactly failure of the paper's promise.
Finite-bit algebraic arithmetic/root isolation remain a separate obligation. -/
namespace Blotto.PlayerSpecificRealAlgorithm
open PRGRealRAMExecution PlayerSpecificCubic PlayerSpecificCells PlayerSpecificRecognition
open PlayerSpecificRealPreparation
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 4000000

structure Strategy {n : ℕ} (i : RationalPlayerSpecificInput n) where
  gamma : ℝ
  scale : ℝ
  valid : ValidParameters i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma scale
  prepared : Prepared (toInput i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma scale
    (by exact_mod_cast i.budget_pos) (by exact_mod_cast i.budget_le) valid)

noncomputable def Strategy.input {n : ℕ} {i : RationalPlayerSpecificInput n} (s : Strategy i) : PlayerSpecificInput n :=
  toInput i.valuesA.values i.valuesB.values (i.budget : ℝ) s.gamma s.scale
    (by exact_mod_cast i.budget_pos) (by exact_mod_cast i.budget_le) s.valid

noncomputable def accept {n : ℕ} (i : RationalPlayerSpecificInput n) (c : Cell) (gamma : ℝ)
    (h : (PlayerSpecificRationalRecognition.run i).1=some (c,gamma)) : Run (Strategy i) :=
  let scale := candidateScale c.state.coefficients (i.budget : ℝ) gamma
  have valid := PlayerSpecificRationalRecognition.sound i c gamma h
  let accepted := toInput i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma scale
    (by exact_mod_cast i.budget_pos) (by exact_mod_cast i.budget_le) valid
  let v := FixedArrayTable.ofFn (fun j => (i.valuesA.weight j : ℝ))
  let w := FixedArrayTable.ofFn (fun j => (i.valuesB.weight j : ℝ))
  let prepared := prepare accepted v w (by funext j; exact FixedArrayTable.read_ofFn _ j)
    (by funext j; exact FixedArrayTable.read_ofFn _ j) gamma scale (i.budget : ℝ) rfl rfl rfl
  ⟨⟨gamma,scale,valid,prepared.value⟩,prepared.trace++
    [.storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3,.control,.control,.control,.control]⟩

theorem accept_cost {n : ℕ} (i : RationalPlayerSpecificInput n) (c : Cell) (gamma : ℝ)
    (h : (PlayerSpecificRationalRecognition.run i).1=some (c,gamma)) : (accept i c gamma h).cost≤32*n+25 := by
  have hp := prepare_cost
    (toInput i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma
      (candidateScale c.state.coefficients (i.budget : ℝ) gamma)
      (by exact_mod_cast i.budget_pos) (by exact_mod_cast i.budget_le)
      (PlayerSpecificRationalRecognition.sound i c gamma h))
    (FixedArrayTable.ofFn (fun j => (i.valuesA.weight j : ℝ)))
    (FixedArrayTable.ofFn (fun j => (i.valuesB.weight j : ℝ)))
    (by funext j; exact FixedArrayTable.read_ofFn _ j) (by funext j; exact FixedArrayTable.read_ofFn _ j)
    gamma (candidateScale c.state.coefficients (i.budget : ℝ) gamma) (i.budget : ℝ) rfl rfl rfl
  change cost (_++_)≤_
  rw [cost_append]
  change _+8≤_
  change cost _≤32*n+17 at hp
  omega

noncomputable def run {n : ℕ} (i : RationalPlayerSpecificInput n) : Option (Strategy i)×ℕ :=
  let recognized := PlayerSpecificRationalRecognition.run i
  match h : recognized.1 with
  | none => (none,recognized.2+8)
  | some result =>
    let prepared := accept i result.1 result.2 h
    (some prepared.value,recognized.2+(16*n+16)+prepared.cost+16)

theorem work {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run i).2≤8192*(n+1)*(binaryWordWidth (n+1)+2) := by
  have hr := PlayerSpecificRationalRecognition.work i
  have hL := Nat.mul_le_mul_left (n+1) (by omega : 2≤binaryWordWidth (n+1)+2)
  unfold run
  dsimp only
  split
  · nlinarith only [hr,hL]
  · rename_i result h
    have hp := accept_cost i result.1 result.2 h
    change (PlayerSpecificRationalRecognition.run i).2+(16*n+16)+(accept i result.1 result.2 h).cost+16≤_
    nlinarith only [hr,hL,hp]

theorem rejection_iff {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run i).1=none ↔ ¬∃ gamma scale,
      ValidParameters i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma scale := by
  rw [← PlayerSpecificRationalRecognition.rejection_iff i]
  unfold run
  dsimp only
  split
  · rename_i h
    simp only [h]
  · rename_i result h
    simp only [h,Option.some_ne_none]

noncomputable def draw {n : ℕ} {i : RationalPlayerSpecificInput n} (s : Strategy i)
    (firstPlayer : Bool) (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  PlayerSpecificRealSampler.draw s.prepared firstPlayer seed

theorem draw_cost {n : ℕ} {i : RationalPlayerSpecificInput n} (s : Strategy i)
    (firstPlayer : Bool) (seed : RealLottoSeed n) : (draw s firstPlayer seed).cost≤240*n+428198 :=
  PlayerSpecificRealSampler.draw_cost s.prepared firstPlayer seed

theorem draw_budget {n : ℕ} {i : RationalPlayerSpecificInput n} (s : Strategy i)
    (firstPlayer : Bool) (seed : RealLottoSeed n) (hSeed : realGroupSeedValid seed.2) :
    FullBudget (if firstPlayer then 1 else (i.budget : ℝ)) (draw s firstPlayer seed).value.read :=
  PlayerSpecificRealSampler.draw_budget s.prepared firstPlayer seed hSeed

theorem equilibrium {n : ℕ} {i : RationalPlayerSpecificInput n} (s : Strategy i) :
    Supported 1 s.input.lawA ∧ Supported (i.budget : ℝ) s.input.lawB ∧
    regret i.valuesA.values 1 s.input.lawA s.input.lawB=0 ∧
    regret i.valuesB.values (i.budget : ℝ) s.input.lawB s.input.lawA=0 := by
  have h := PlayerSpecificEquilibrium.exact_nash s.input
  exact ⟨s.input.lawA_supported,s.input.lawB_supported,h.1,h.2.1⟩

theorem draw_law {n : ℕ} {i : RationalPlayerSpecificInput n} (s : Strategy i) (firstPlayer : Bool) :
    Measure.map (fun seed => (draw s firstPlayer seed).value.read)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
      (if firstPlayer then (s.input.lawA : Measure (Allocation n)) else (s.input.lawB : Measure (Allocation n))) :=
  PlayerSpecificRealSampler.draw_law s.prepared firstPlayer

theorem independent_draw_law {n : ℕ} {i : RationalPlayerSpecificInput n} (s : Strategy i) :
    Measure.map (Prod.map (fun seed => (draw s true seed).value.read) (fun seed => (draw s false seed).value.read))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (s.input.lawA : Measure (Allocation n)).prod (s.input.lawB : Measure (Allocation n)) :=
  PlayerSpecificRealSampler.draw_product_law s.prepared

theorem actual_contract {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run i).2≤8192*(n+1)*(binaryWordWidth (n+1)+2) ∧
    ((run i).1=none ↔ ¬∃ gamma scale,
      ValidParameters i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma scale) ∧
    ∀ s,(run i).1=some s →
      (Supported 1 s.input.lawA ∧ Supported (i.budget : ℝ) s.input.lawB ∧
        regret i.valuesA.values 1 s.input.lawA s.input.lawB=0 ∧
        regret i.valuesB.values (i.budget : ℝ) s.input.lawB s.input.lawA=0) ∧
      Measure.map (Prod.map (fun seed => (draw s true seed).value.read) (fun seed => (draw s false seed).value.read))
        ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
          (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
        (s.input.lawA : Measure (Allocation n)).prod (s.input.lawB : Measure (Allocation n)) ∧
      ∀ firstPlayer seed,(draw s firstPlayer seed).cost≤240*n+428198 ∧
        (realGroupSeedValid seed.2 → FullBudget (if firstPlayer then 1 else (i.budget : ℝ))
          (draw s firstPlayer seed).value.read) := by
  exact ⟨work i,rejection_iff i,fun s _ => ⟨equilibrium s,independent_draw_law s,
    fun player seed => ⟨draw_cost s player seed,draw_budget s player seed⟩⟩⟩

end Blotto.PlayerSpecificRealAlgorithm
