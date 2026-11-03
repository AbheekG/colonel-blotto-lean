import Blotto.PlayerSpecificRealPreparation

/-! Cached player-specific draws execute the generic maintained-array Lotto
source and the reached terminal coupling. The same actual stored arrays are
used on every draw. Whole-player independence is proved from product seeds. -/
namespace Blotto.PlayerSpecificRealSampler
open PRGRealRAMExecution RealPRGNativeFactoryExecution PlayerSpecificRealPreparation
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable def source {n : ℕ} (i : PlayerSpecificInput n) (firstPlayer : Bool) : LottoResourceSystem n :=
  if firstPlayer then i.systemA else i.systemB

noncomputable def system {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i)
    (firstPlayer : Bool) : LottoResourceSystem n where
  B := if firstPlayer then 1 else p.budget
  length := p.lengths.read
  initial := if firstPlayer then p.initialA.read else p.initialB.read
  B_pos := by
    cases firstPlayer
    · exact p.budget_correct.symm ▸ i.budget_pos
    · norm_num
  length_pos := by rw [p.lengths_correct]; exact i.length_pos
  length_le := by
    rw [p.lengths_correct,p.budget_correct]
    cases firstPlayer
    · exact i.endpoint
    · exact fun j => (i.endpoint j).trans i.budget_le
  initial_box := by
    rw [p.initialA_correct,p.initialB_correct,p.lengths_correct]
    cases firstPlayer
    · exact i.systemB.initial_box
    · exact i.systemA.initial_box
  initial_sum := by
    rw [p.initialA_correct,p.initialB_correct,p.budget_correct]
    cases firstPlayer
    · exact i.systemB.initial_sum
    · exact i.systemA.initial_sum

theorem system_eq {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i) (firstPlayer : Bool) :
    system p firstPlayer=source i firstPlayer := by
  have ext (s t : LottoResourceSystem n) (hB : s.B=t.B) (hL : s.length=t.length)
      (hI : s.initial=t.initial) : s=t := by
    cases s; cases t; cases hB; cases hL; cases hI; rfl
  apply ext
  · cases firstPlayer <;> simp only [system,source,Bool.false_eq_true,ite_false,ite_true,p.budget_correct] <;> rfl
  · cases firstPlayer <;> exact p.lengths_correct
  · cases firstPlayer
    · exact p.initialB_correct
    · exact p.initialA_correct

noncomputable def draw {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i) (firstPlayer : Bool)
    (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  let initial := if firstPlayer then p.initialA else p.initialB
  join (⟨(),[.control,.control,.control,.control,.storeCell 0,.storeCell 1,.storeCell 2,
    .control,.control,.control,.control,.control]⟩ : Run Unit)
    (RealPRGGlobalExecution.lottoDrawStored (system p firstPlayer) p.lengths initial rfl
      (by cases firstPlayer <;> rfl) seed)

theorem draw_cost {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i) (firstPlayer : Bool) (seed : RealLottoSeed n) :
    (draw p firstPlayer seed).cost≤240*n+428198 := by
  have h := RealPRGGlobalExecution.lottoDrawStored_cost (system p firstPlayer) p.lengths
    (if firstPlayer then p.initialA else p.initialB) rfl (by cases firstPlayer <;> rfl) seed
  unfold draw
  rw [join_cost]
  change 12+_≤_
  omega

theorem draw_value {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i) (firstPlayer : Bool) (seed : RealLottoSeed n) :
    (draw p firstPlayer seed).value.read=(source i firstPlayer).realSample seed := by
  have h := RealPRGGlobalExecution.lottoDrawStored_value (system p firstPlayer) p.lengths
    (if firstPlayer then p.initialA else p.initialB) rfl (by cases firstPlayer <;> rfl) seed
  exact h.trans (congrArg (fun s => s.realSample seed) (system_eq p firstPlayer))

theorem draw_budget {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i) (firstPlayer : Bool)
    (seed : RealLottoSeed n) (hSeed : realGroupSeedValid seed.2) :
    FullBudget (if firstPlayer then 1 else i.budget) (draw p firstPlayer seed).value.read := by
  rw [draw_value]
  have h := (source i firstPlayer).realSample_fullBudget seed hSeed
  cases firstPlayer <;> exact h

theorem draw_law {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i) (firstPlayer : Bool) :
    Measure.map (fun seed => (draw p firstPlayer seed).value.read)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
      (if firstPlayer then (i.lawA : Measure (Allocation n)) else (i.lawB : Measure (Allocation n))) := by
  simp_rw [draw_value]
  cases firstPlayer
  · exact i.systemB.realSample_law
  · exact i.systemA.realSample_law

theorem draw_product_law {n : ℕ} {i : PlayerSpecificInput n} (p : Prepared i) :
    Measure.map (Prod.map (fun seed => (draw p true seed).value.read)
      (fun seed => (draw p false seed).value.read))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (i.lawA : Measure (Allocation n)).prod (i.lawB : Measure (Allocation n)) := by
  have hA : (fun seed => (draw p true seed).value.read)=i.systemA.realSample := funext (draw_value p true)
  have hB : (fun seed => (draw p false seed).value.read)=i.systemB.realSample := funext (draw_value p false)
  rw [hA,hB,← Measure.map_prod_map _ _ i.systemA.realSample_measurable i.systemB.realSample_measurable,
    i.systemA.realSample_law,i.systemB.realSample_law]
  rfl

theorem exact_contract {n : ℕ} (i : PlayerSpecificInput n) (v w : FixedArrayTable n ℝ)
    (hV : v.read=i.valuesA.weight) (hW : w.read=i.valuesB.weight)
    (gamma scale budget : ℝ) (hG : gamma=i.gamma) (hS : scale=i.scale) (hB : budget=i.budget) :
    (prepare i v w hV hW gamma scale budget hG hS hB).cost≤32*n+17 ∧
    regret i.valuesA 1 i.lawA i.lawB=0 ∧ regret i.valuesB i.budget i.lawB i.lawA=0 ∧
    (∀ firstPlayer seed,(draw (prepare i v w hV hW gamma scale budget hG hS hB).value firstPlayer seed).cost≤240*n+428198 ∧
      (realGroupSeedValid seed.2 → FullBudget (if firstPlayer then 1 else i.budget)
        (draw (prepare i v w hV hW gamma scale budget hG hS hB).value firstPlayer seed).value.read)) := by
  have hn := PlayerSpecificEquilibrium.exact_nash i
  exact ⟨prepare_cost i v w hV hW gamma scale budget hG hS hB,hn.1,hn.2.1,
    fun player seed => ⟨draw_cost _ player seed,draw_budget _ player seed⟩⟩

end Blotto.PlayerSpecificRealSampler
