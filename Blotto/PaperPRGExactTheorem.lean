import Blotto.PaperPRGRealInput

/-! Theorem 2.1 as a single statement. `exact_contract` proves the equilibrium
for the mathematical laws `richLaw` and `poorLaw`; this statement also records
that these are the laws of the actual draws, with independent player seeds. -/
namespace Blotto.PaperPRGExactTheorem
open PaperPRGRealInput
open MeasureTheory
set_option autoImplicit false

theorem paper_theorem {n : ℕ} (i : PRGInput n) (values : FixedArrayTable n ℝ)
    (hV : values.read=i.values.weight) (budget : ℝ) (hB : budget=i.b) :
    (prepare i values hV budget hB).cost ≤ 8*n+14 ∧
    (∀ rich, Measure.map (fun seed => (draw (prepare i values hV budget hB).value rich seed).value.read)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
        (if rich then (i.richLaw : Measure (Allocation n)) else (i.poorLaw : Measure (Allocation n)))) ∧
    Measure.map (Prod.map (fun seed => (draw (prepare i values hV budget hB).value true seed).value.read)
      (fun seed => (draw (prepare i values hV budget hB).value false seed).value.read))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (i.richLaw : Measure (Allocation n)).prod (i.poorLaw : Measure (Allocation n)) ∧
    regret i.values 1 i.richLaw i.poorLaw=0 ∧ regret i.values i.b i.poorLaw i.richLaw=0 ∧
    expected i.values i.richLaw i.poorLaw=1-i.b/2 ∧ expected i.values i.poorLaw i.richLaw=i.b/2 ∧
    ∀ rich seed, (draw (prepare i values hV budget hB).value rich seed).cost ≤ 240*n+428198 ∧
      (realGroupSeedValid seed.2 → FullBudget (if rich then 1 else i.b)
        (draw (prepare i values hV budget hB).value rich seed).value.read) := by
  have h := exact_contract i values hV budget hB
  exact ⟨h.1,draw_law _,draw_product_law _,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

end Blotto.PaperPRGExactTheorem
