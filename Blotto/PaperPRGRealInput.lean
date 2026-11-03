import Blotto.RealPRGGlobalExecution

/-! The normalized paper theorem accepts arbitrary real input data. This
wrapper builds the two retained arrays from the supplied real value array;
the mathematical PRG object supplies only erased correctness proofs. -/
namespace Blotto.PaperPRGRealInput
open PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Prepared {n : ℕ} (i : PRGInput n) where
  budget : ℝ
  lengths : FixedArrayTable n ℝ
  initial : FixedArrayTable n ℝ
  budget_correct : budget=i.b
  lengths_correct : lengths.read=i.richSystem.length
  initial_correct : initial.read=i.poorSystem.initial

noncomputable def prepare {n : ℕ} (i : PRGInput n) (values : FixedArrayTable n ℝ)
    (hV : values.read=i.values.weight) (budget : ℝ) (hB : budget=i.b) : Run (Prepared i) :=
  let loaded := RealPRGInputExecution.scalar 0 budget
  let two := RealPRGInputExecution.scalar 1 2
  let lengths := RealPRGInputExecution.multiplyArray two.value values
  let initial := RealPRGInputExecution.multiplyArray loaded.value lengths.value
  have hL : lengths.value.read=i.richSystem.length := by
    rw [RealPRGInputExecution.multiplyArray_value]
    simp only [two,RealPRGInputExecution.scalar,hV,PRGInput.richSystem]
  have hI : initial.value.read=i.poorSystem.initial := by
    rw [RealPRGInputExecution.multiplyArray_value,hL]
    simp only [loaded,RealPRGInputExecution.scalar,hB,PRGInput.richSystem,PRGInput.poorSystem]
  join loaded (join two (join lengths (join initial
    ⟨⟨loaded.value,lengths.value,initial.value,hB,hL,hI⟩,
      [.storeCell 0,.storeCell 1,.storeCell 2,.control]⟩)))

theorem prepare_cost {n : ℕ} (i : PRGInput n) (values : FixedArrayTable n ℝ)
    (hV : values.read=i.values.weight) (budget : ℝ) (hB : budget=i.b) :
    (prepare i values hV budget hB).cost ≤ 8*n+14 := by
  have hL := RealPRGInputExecution.multiplyArray_cost (RealPRGInputExecution.scalar 1 2).value values
  have hI := RealPRGInputExecution.multiplyArray_cost (RealPRGInputExecution.scalar 0 budget).value
    (RealPRGInputExecution.multiplyArray (RealPRGInputExecution.scalar 1 2).value values).value
  unfold prepare
  rw [join_cost,join_cost,join_cost,join_cost]
  change 1+(1+(_+(_+4))) ≤ _
  omega

noncomputable def source {n : ℕ} (i : PRGInput n) (rich : Bool) : LottoResourceSystem n :=
  if rich then i.richSystem else i.poorSystem

noncomputable def system {n : ℕ} {i : PRGInput n} (p : Prepared i) (rich : Bool) : LottoResourceSystem n where
  B := if rich then 1 else p.budget
  length := p.lengths.read
  initial := if rich then p.lengths.read else p.initial.read
  B_pos := by cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true,p.budget_correct]; exact i.b_pos; norm_num
  length_pos := by rw [p.lengths_correct]; exact i.richSystem.length_pos
  length_le := by
    rw [p.lengths_correct,p.budget_correct]
    cases rich
    · exact i.small_fields
    · exact i.richSystem.length_le
  initial_box := by
    rw [p.lengths_correct,p.initial_correct]
    cases rich
    · exact i.poorSystem.initial_box
    · exact i.richSystem.initial_box
  initial_sum := by
    rw [p.lengths_correct,p.initial_correct,p.budget_correct]
    cases rich
    · exact i.poorSystem.initial_sum
    · exact i.richSystem.initial_sum

theorem system_eq {n : ℕ} {i : PRGInput n} (p : Prepared i) (rich : Bool) : system p rich=source i rich := by
  have ext (s t : LottoResourceSystem n) (hB : s.B=t.B) (hL : s.length=t.length)
      (hI : s.initial=t.initial) : s=t := by
    cases s; cases t; cases hB; cases hL; cases hI; rfl
  apply ext
  · cases rich <;> simp only [system,source,Bool.false_eq_true,ite_false,ite_true,p.budget_correct] <;> rfl
  · cases rich <;> exact p.lengths_correct
  · cases rich
    · exact p.initial_correct
    · exact p.lengths_correct

noncomputable def draw {n : ℕ} {i : PRGInput n} (p : Prepared i) (rich : Bool)
    (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  let initial := if rich then p.lengths else p.initial
  join (⟨(),[.control,.control,.control,.control,.storeCell 0,.storeCell 1,.storeCell 2,
    .control,.control,.control,.control,.control]⟩ : Run Unit)
    (RealPRGGlobalExecution.lottoDrawStored (system p rich) p.lengths initial rfl
      (by cases rich <;> rfl) seed)

theorem draw_cost {n : ℕ} {i : PRGInput n} (p : Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    (draw p rich seed).cost ≤ 240*n+428198 := by
  have h := RealPRGGlobalExecution.lottoDrawStored_cost (system p rich) p.lengths
    (if rich then p.lengths else p.initial) rfl (by cases rich <;> rfl) seed
  unfold draw
  rw [join_cost]
  change 12+_ ≤ _
  omega

theorem draw_value {n : ℕ} {i : PRGInput n} (p : Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    (draw p rich seed).value.read=(source i rich).realSample seed := by
  have h := RealPRGGlobalExecution.lottoDrawStored_value (system p rich) p.lengths
    (if rich then p.lengths else p.initial) rfl (by cases rich <;> rfl) seed
  exact h.trans (congrArg (fun s => s.realSample seed) (system_eq p rich))

theorem draw_budget {n : ℕ} {i : PRGInput n} (p : Prepared i) (rich : Bool)
    (seed : RealLottoSeed n) (hSeed : realGroupSeedValid seed.2) :
    FullBudget (if rich then 1 else i.b) (draw p rich seed).value.read := by
  rw [draw_value]
  have h := (source i rich).realSample_fullBudget seed hSeed
  cases rich <;> exact h

theorem draw_law {n : ℕ} {i : PRGInput n} (p : Prepared i) (rich : Bool) :
    Measure.map (fun seed => (draw p rich seed).value.read)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
        (if rich then (i.richLaw : Measure (Allocation n)) else (i.poorLaw : Measure (Allocation n))) := by
  simp_rw [draw_value]
  cases rich
  · exact i.poorSystem.realSample_law
  · exact i.richSystem.realSample_law

theorem draw_product_law {n : ℕ} {i : PRGInput n} (p : Prepared i) :
    Measure.map (Prod.map (fun seed => (draw p true seed).value.read)
      (fun seed => (draw p false seed).value.read))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (i.richLaw : Measure (Allocation n)).prod (i.poorLaw : Measure (Allocation n)) := by
  have hRich : (fun seed => (draw p true seed).value.read)=i.realRichSample :=
    funext (draw_value p true)
  have hPoor : (fun seed => (draw p false seed).value.read)=i.realPoorSample :=
    funext (draw_value p false)
  rw [hRich,hPoor]
  exact i.realOutputs_product_law

theorem exact_contract {n : ℕ} (i : PRGInput n) (values : FixedArrayTable n ℝ)
    (hV : values.read=i.values.weight) (budget : ℝ) (hB : budget=i.b) :
    (prepare i values hV budget hB).cost ≤ 8*n+14 ∧
    regret i.values 1 i.richLaw i.poorLaw=0 ∧ regret i.values i.b i.poorLaw i.richLaw=0 ∧
    expected i.values i.richLaw i.poorLaw=1-i.b/2 ∧ expected i.values i.poorLaw i.richLaw=i.b/2 ∧
    ∀ rich seed, (draw (prepare i values hV budget hB).value rich seed).cost ≤ 240*n+428198 ∧
      (realGroupSeedValid seed.2 → FullBudget (if rich then 1 else i.b)
        (draw (prepare i values hV budget hB).value rich seed).value.read) := by
  refine ⟨prepare_cost i values hV budget hB,i.equilibrium.1,i.equilibrium.2.1,
    i.equilibrium.2.2.1,i.equilibrium.2.2.2,?_⟩
  intro rich seed
  exact ⟨draw_cost _ _ _,draw_budget _ _ _⟩

end Blotto.PaperPRGRealInput
