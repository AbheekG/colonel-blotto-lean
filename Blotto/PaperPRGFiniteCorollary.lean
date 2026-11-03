import Blotto.PaperPRGContract

/-! Corollary 2.5 as a single statement. `finite_contract` bounds the regret of
the laws of `sample` and the budget of the returned frame `output`; here the
frame is shown to decode to exactly the sampled rational row, and the two
players' draws use disjoint fair-bit blocks. -/
namespace Blotto.PaperPRGFiniteCorollary
open PaperPRGContract
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem output_decodes {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    BinaryRatListFrame.readRow (PaperPRGDataSampler.output p rich bits)=
      some (n,List.ofFn (PaperPRGDataSampler.sample p rich bits).allocation,[]) := by
  rw [PaperPRGDataSampler.output_data,NativePRGPreparedSampler.output_data,PaperPRGDataSampler.sample_data]
  cases rich with
  | false =>
    simp only [Bool.false_eq_true,ite_false,NativePRGPreparedSampler.sample,
      RationalPRGOriginalInput.storedPoorSample_allocation]
    simpa only [List.append_nil] using p.source.poorOutput_readback p.precision bits []
  | true =>
    simp only [ite_true,NativePRGPreparedSampler.sample,
      RationalPRGOriginalInput.storedRichSample_allocation]
    simpa only [List.append_nil] using p.source.richOutput_readback p.precision bits []

theorem paper_corollary {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) :
    let p := NativePRGPreparedSampler.ofInput i a.precision
    let R := RationalLottoResourceSystem.sampleBitBudget n a.precision
    a.precision=⌈Real.logb 2 (32/a.real)⌉₊ ∧
    regret i.realValues (i.a:ℝ) (PaperPRGDataSampler.law p true) (PaperPRGDataSampler.law p false)<a.real ∧
    regret i.realValues (i.b:ℝ) (PaperPRGDataSampler.law p false) (PaperPRGDataSampler.law p true)<a.real ∧
    MeasureTheory.Measure.map (fun bits =>
      ((PaperPRGDataSampler.sample p true (firstBitBlock R R bits)).realAllocation,
        (PaperPRGDataSampler.sample p false (secondBitBlock R R bits)).realAllocation))
      (fairBitLaw (R+R) : MeasureTheory.Measure (Fin (R+R) → Bool)) =
      (PaperPRGDataSampler.law p true : MeasureTheory.Measure (Allocation n)).prod
        (PaperPRGDataSampler.law p false : MeasureTheory.Measure (Allocation n)) ∧
    R ≤ 3*n+5*⌈Real.logb 2 (1/a.real)⌉₊+3025 ∧
    PRGPaperSplitPreparationCost.prepare (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a)=some ⟨n,p⟩ ∧
    PRGPaperSplitPreparationCost.work model primitive (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a) ≤
      preparationBound i a model c ∧
    ∀ rich (bits : Fin R → Bool),
      BinaryRatListFrame.readRow (PaperPRGDataSampler.output p rich bits)=
        some (n,List.ofFn (PaperPRGDataSampler.sample p rich bits).allocation,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget n (if rich then i.a else i.b) (PaperPRGDataSampler.output p rich bits) ∧
      (PaperPRGDataSampler.output p rich bits).length ≤ 8*n*PRGPaperDrawCost.accuracyWidth i ⌈Real.logb 2 (1/a.real)⌉₊ ∧
      PaperPRGControllerRecords.work p model primitive c rich bits ≤
        drawBound i model c ⌈Real.logb 2 (1/a.real)⌉₊ (NativePRGPreparedSampler.header n).length := by
  intro p R
  obtain ⟨hK,hA,hB,hR,hPrepare,hWork,hDraw⟩ := finite_contract i a model primitive c hPrimitive
  exact ⟨hK,hA,hB,independent_laws p,hR,hPrepare,hWork,
    fun rich bits => ⟨output_decodes p rich bits,hDraw rich bits⟩⟩

end Blotto.PaperPRGFiniteCorollary
