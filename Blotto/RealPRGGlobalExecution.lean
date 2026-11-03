import Blotto.RealPRGTerminalExecution
import Blotto.RealPRGResourceExecution
import Blotto.RealPRGInputExecution

/-! The complete exact-real PRG sampler in the declared RAM model joins
actual original-input preparation, fixed-region mutable resource execution,
charged terminal classification/packing/routing, cached grouped sampling,
coordinate emission and original scaling. Runtime fields of the prepared
systems are native array readers. Mathematical witnesses occur in erased
legality/readback proofs; no construction or runtime-price oracle is supplied.
The bounds concern named exact-real and word/cell operations, not Lean-host
execution, IEEE arithmetic or the separately required finite-binary machine. -/

namespace Blotto.RealPRGGlobalExecution
open PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
open MeasureTheory
open scoped BigOperators Classical

noncomputable def lottoDraw {n : ℕ} (i : LottoResourceSystem n)
    (lengths : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  let rounded := RealPRGResourceExecution.source i seed.1
  let terminal := i.terminal rounded.value.read (RealPRGResourceExecution.source_valid i seed.1)
  let drawn := RealPRGTerminalExecution.draw terminal lengths rounded.value hL rfl seed.2
  join rounded (join
    (⟨(), [.storeCell 0, .storeCell 1, .storeCell 2, .control, .control, .control]⟩ : Run Unit) drawn)

theorem terminal_congr {n : ℕ} (i : LottoResourceSystem n) (first second : Allocation n)
    (hFirst : i.Valid first) (hSecond : i.Valid second) (h : first = second) :
    i.terminal first hFirst = i.terminal second hSecond := by
  cases h
  rfl

theorem lottoDraw_value {n : ℕ} (i : LottoResourceSystem n)
    (lengths : FixedArrayTable n ℝ) (hL : lengths.read = i.length) (seed : RealLottoSeed n) :
    (lottoDraw i lengths hL seed).value.read = i.realSample seed := by
  have h := RealPRGTerminalExecution.draw_value
    (i.terminal (RealPRGResourceExecution.source i seed.1).value.read
      (RealPRGResourceExecution.source_valid i seed.1))
    lengths (RealPRGResourceExecution.source i seed.1).value hL rfl seed.2
  have hTerminal := terminal_congr i (RealPRGResourceExecution.source i seed.1).value.read
    (i.realPhase seed.1) (RealPRGResourceExecution.source_valid i seed.1)
    (i.realPhase_valid seed.1) (RealPRGResourceExecution.source_value i seed.1)
  exact h.trans (congrArg (fun terminal => terminal.realSample seed.2) hTerminal)

theorem lottoDraw_cost {n : ℕ} (i : LottoResourceSystem n)
    (lengths : FixedArrayTable n ℝ) (hL : lengths.read = i.length) (seed : RealLottoSeed n) :
    (lottoDraw i lengths hL seed).cost ≤ 243 * n + 428191 := by
  have hr := RealPRGResourceExecution.source_cost i seed.1
  have ht := RealPRGTerminalExecution.draw_cost
    (i.terminal (RealPRGResourceExecution.source i seed.1).value.read
      (RealPRGResourceExecution.source_valid i seed.1))
    lengths (RealPRGResourceExecution.source i seed.1).value hL rfl seed.2
  unfold lottoDraw
  rw [join_cost, join_cost]
  change _ + (6 + _) ≤ _
  omega

theorem lottoDraw_law {n : ℕ} (i : LottoResourceSystem n)
    (lengths : FixedArrayTable n ℝ) (hL : lengths.read = i.length) :
    Measure.map (fun seed => (lottoDraw i lengths hL seed).value.read)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
        (i.law : Measure (Allocation n)) := by
  have h : (fun seed => (lottoDraw i lengths hL seed).value.read) = i.realSample :=
    funext (lottoDraw_value i lengths hL)
  rw [h]
  exact i.realSample_law

theorem lottoDraw_fullBudget {n : ℕ} (i : LottoResourceSystem n)
    (lengths : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (seed : RealLottoSeed n) (hs : realGroupSeedValid seed.2) :
    FullBudget i.B (lottoDraw i lengths hL seed).value.read := by
  rw [lottoDraw_value]
  exact i.realSample_fullBudget seed hs

noncomputable def preparedDraw {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    Run (FixedArrayTable n ℝ) :=
  let normalized := if rich then lottoDraw prepared.rich prepared.lengths prepared.rich_length.symm seed
    else lottoDraw prepared.poor prepared.lengths prepared.poor_length.symm seed
  join (⟨(), [.control, .control]⟩ : Run Unit)
    (join normalized (RealPRGPackingExecution.scale prepared.scale normalized.value))

theorem preparedDraw_value {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    (preparedDraw prepared rich seed).value.read =
      if rich then i.realRichSample seed else i.realPoorSample seed := by
  funext j
  simp only [preparedDraw, join_value, RealPRGPackingExecution.scale_value]
  cases rich
  · simp only [Bool.false_eq_true, ite_false, lottoDraw_value, prepared.poor_correct, prepared.scale_correct]
    have h := congrFun (i.realPoorSample_scale seed) j
    change i.realPoorSample seed j = (i.a : ℝ) * i.normalizedInput.real.poorSystem.realSample seed j at h
    exact h.symm
  · simp only [ite_true, lottoDraw_value, prepared.rich_correct, prepared.scale_correct]
    have h := congrFun (i.realRichSample_scale seed) j
    change i.realRichSample seed j = (i.a : ℝ) * i.normalizedInput.real.richSystem.realSample seed j at h
    exact h.symm

theorem preparedDraw_cost {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    (preparedDraw prepared rich seed).cost ≤ 248 * n + 428195 := by
  have hNorm : (if rich then lottoDraw prepared.rich prepared.lengths prepared.rich_length.symm seed
      else lottoDraw prepared.poor prepared.lengths prepared.poor_length.symm seed).cost ≤ 243 * n + 428191 := by
    cases rich
    · exact lottoDraw_cost _ _ _ _
    · exact lottoDraw_cost _ _ _ _
  unfold preparedDraw
  rw [join_cost, join_cost, RealPRGPackingExecution.scale_cost]
  change 2 + (_ + (5 * n + 2)) ≤ _
  omega

noncomputable def originalDraw {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  let prepared := RealPRGInputExecution.prepare i values hV availableRich availablePoor hA hB
  join prepared (preparedDraw prepared.value rich seed)

theorem originalDraw_value {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    (originalDraw i values hV availableRich availablePoor hA hB rich seed).value.read =
      if rich then i.realRichSample seed else i.realPoorSample seed := preparedDraw_value _ _ _

theorem originalDraw_cost {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    (originalDraw i values hV availableRich availablePoor hA hB rich seed).cost ≤ 256 * n + 428245 := by
  have hp := RealPRGInputExecution.prepare_cost i values hV availableRich availablePoor hA hB
  have hd := preparedDraw_cost (RealPRGInputExecution.prepare i values hV availableRich availablePoor hA hB).value rich seed
  rw [originalDraw, join_cost]
  omega

theorem originalDraw_cost_from_header {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    (originalDraw i values hV availableRich availablePoor hA hB rich seed).cost ≤ 256 * values.data.size + 428245 := by
  rw [values.size]
  exact originalDraw_cost _ _ _ _ _ _ _ _ _

theorem originalDraw_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) (hs : realGroupSeedValid seed.2) :
    FullBudget (if rich then (i.a : ℝ) else (i.b : ℝ))
      (originalDraw i values hV availableRich availablePoor hA hB rich seed).value.read := by
  rw [originalDraw_value]
  cases rich
  · exact i.realPoorSample_fullBudget seed hs
  · exact i.realRichSample_fullBudget seed hs

noncomputable def law {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) : Mixed n :=
  (LottoResourceSystem.realInputLaw n).map
    (fun seed => (originalDraw i values hV availableRich availablePoor hA hB rich seed).value.read)

theorem law_state {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) : law i values hV availableRich availablePoor hA hB rich =
      if rich then i.realRichLaw else i.realPoorLaw := by
  have h : (fun seed => (originalDraw i values hV availableRich availablePoor hA hB rich seed).value.read) =
      fun seed => if rich then i.realRichSample seed else i.realPoorSample seed :=
    funext (originalDraw_value i values hV availableRich availablePoor hA hB rich)
  apply ProbabilityMeasure.toMeasure_injective
  unfold law
  simp only [ProbabilityMeasure.toMeasure_map, h]
  cases rich
  · exact i.realPoorSample_law
  · exact i.realRichSample_law

theorem equilibrium {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    regret i.realValues (i.a : ℝ) (law i values hV availableRich availablePoor hA hB true)
      (law i values hV availableRich availablePoor hA hB false) = 0 ∧
    regret i.realValues (i.b : ℝ) (law i values hV availableRich availablePoor hA hB false)
      (law i values hV availableRich availablePoor hA hB true) = 0 ∧
    expected i.realValues (law i values hV availableRich availablePoor hA hB true)
      (law i values hV availableRich availablePoor hA hB false) = 1 - (i.normalizedInput.b : ℝ) / 2 ∧
    expected i.realValues (law i values hV availableRich availablePoor hA hB false)
      (law i values hV availableRich availablePoor hA hB true) = (i.normalizedInput.b : ℝ) / 2 := by
  rw [law_state, law_state]
  exact i.realEquilibrium

/-- Cached capacities and initial resources are the actual runtime inputs.
The private source copy is followed by the reached terminal preparation. -/
noncomputable def lottoDrawStored {n : ℕ} (i : LottoResourceSystem n)
    (lengths initial : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (hI : initial.read = i.initial) (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  let rounded := RealPRGResourceExecution.sourceStored lengths initial seed.1
  let terminal := i.terminal rounded.value.read
    (RealPRGResourceExecution.sourceStored_valid i lengths initial hL hI seed.1)
  let drawn := RealPRGTerminalExecution.draw terminal lengths rounded.value hL rfl seed.2
  join rounded (join
    (⟨(),[.storeCell 0,.storeCell 1,.storeCell 2,.control,.control,.control]⟩ : Run Unit) drawn)

theorem lottoDrawStored_value {n : ℕ} (i : LottoResourceSystem n)
    (lengths initial : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (hI : initial.read = i.initial) (seed : RealLottoSeed n) :
    (lottoDrawStored i lengths initial hL hI seed).value.read = i.realSample seed := by
  have h := RealPRGTerminalExecution.draw_value
    (i.terminal (RealPRGResourceExecution.sourceStored lengths initial seed.1).value.read
      (RealPRGResourceExecution.sourceStored_valid i lengths initial hL hI seed.1))
    lengths (RealPRGResourceExecution.sourceStored lengths initial seed.1).value hL rfl seed.2
  have ht := terminal_congr i (RealPRGResourceExecution.sourceStored lengths initial seed.1).value.read
    (i.realPhase seed.1) (RealPRGResourceExecution.sourceStored_valid i lengths initial hL hI seed.1)
    (i.realPhase_valid seed.1) (RealPRGResourceExecution.sourceStored_value i lengths initial hL hI seed.1)
  exact h.trans (congrArg (fun terminal => terminal.realSample seed.2) ht)

theorem lottoDrawStored_cost {n : ℕ} (i : LottoResourceSystem n)
    (lengths initial : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (hI : initial.read = i.initial) (seed : RealLottoSeed n) :
    (lottoDrawStored i lengths initial hL hI seed).cost ≤ 240 * n + 428186 := by
  have hr := RealPRGResourceExecution.sourceStored_cost lengths initial seed.1
  have ht := RealPRGTerminalExecution.draw_cost
    (i.terminal (RealPRGResourceExecution.sourceStored lengths initial seed.1).value.read
      (RealPRGResourceExecution.sourceStored_valid i lengths initial hL hI seed.1))
    lengths (RealPRGResourceExecution.sourceStored lengths initial seed.1).value hL rfl seed.2
  unfold lottoDrawStored
  rw [join_cost,join_cost]
  change _ + (6 + _) ≤ _
  omega

/-- One draw reuses the arrays and scalar fields constructed by `prepare`.
Both player choices execute the same complete source/terminal/emission path. -/
noncomputable def cachedDraw {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    Run (FixedArrayTable n ℝ) :=
  let normalized := if rich then
    lottoDrawStored prepared.rich prepared.lengths prepared.lengths prepared.rich_length.symm
      prepared.rich_initial.symm seed
    else lottoDrawStored prepared.poor prepared.lengths prepared.poorInitial prepared.poor_length.symm
      prepared.poor_initial.symm seed
  join (⟨(),[.control,.control]⟩ : Run Unit)
    (join normalized (RealPRGPackingExecution.scale prepared.scale normalized.value))

theorem cachedDraw_value {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    (cachedDraw prepared rich seed).value.read =
      if rich then i.realRichSample seed else i.realPoorSample seed := by
  funext j
  simp only [cachedDraw,join_value,RealPRGPackingExecution.scale_value]
  cases rich
  · simp only [Bool.false_eq_true,ite_false,lottoDrawStored_value,prepared.poor_correct,prepared.scale_correct]
    exact (congrFun (i.realPoorSample_scale seed) j).symm
  · simp only [ite_true,lottoDrawStored_value,prepared.rich_correct,prepared.scale_correct]
    exact (congrFun (i.realRichSample_scale seed) j).symm

theorem cachedDraw_cost {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    (cachedDraw prepared rich seed).cost ≤ 245 * n + 428190 := by
  have hn : (if rich then
      lottoDrawStored prepared.rich prepared.lengths prepared.lengths prepared.rich_length.symm prepared.rich_initial.symm seed
      else lottoDrawStored prepared.poor prepared.lengths prepared.poorInitial prepared.poor_length.symm prepared.poor_initial.symm seed).cost
        ≤ 240 * n + 428186 := by
    cases rich
    · exact lottoDrawStored_cost prepared.poor prepared.lengths prepared.poorInitial
        prepared.poor_length.symm prepared.poor_initial.symm seed
    · exact lottoDrawStored_cost prepared.rich prepared.lengths prepared.lengths
        prepared.rich_length.symm prepared.rich_initial.symm seed
  unfold cachedDraw
  rw [join_cost,join_cost,RealPRGPackingExecution.scale_cost]
  change 2 + (_ + (5 * n + 2)) ≤ _
  omega

theorem cachedDraw_cost_from_header {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n) :
    (cachedDraw prepared rich seed).cost ≤ 245 * prepared.lengths.data.size + 428190 := by
  rw [prepared.lengths.size]
  exact cachedDraw_cost prepared rich seed

theorem cachedDraw_measurable {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) :
    Measurable (fun seed => (cachedDraw prepared rich seed).value.read) := by
  have h : (fun seed => (cachedDraw prepared rich seed).value.read) =
      (fun seed => if rich then i.realRichSample seed else i.realPoorSample seed) :=
    funext (cachedDraw_value prepared rich)
  rw [h]
  cases rich
  · exact i.realPoorSample_measurable
  · exact i.realRichSample_measurable

theorem cachedDraw_fullBudget {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n)
    (hs : realGroupSeedValid seed.2) :
    FullBudget (if rich then (i.a : ℝ) else (i.b : ℝ)) (cachedDraw prepared rich seed).value.read := by
  rw [cachedDraw_value]
  cases rich
  · exact i.realPoorSample_fullBudget seed hs
  · exact i.realRichSample_fullBudget seed hs

theorem cachedDraw_feasible {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) (seed : RealLottoSeed n)
    (hs : realGroupSeedValid seed.2) :
    Feasible (if rich then (i.a : ℝ) else (i.b : ℝ)) (cachedDraw prepared rich seed).value.read :=
  fullBudget_feasible (cachedDraw_fullBudget prepared rich seed hs)

noncomputable def cachedLaw {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) : Mixed n :=
  (LottoResourceSystem.realInputLaw n).map (fun seed => (cachedDraw prepared rich seed).value.read)

theorem cachedLaw_state {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) (rich : Bool) :
    cachedLaw prepared rich = if rich then i.realRichLaw else i.realPoorLaw := by
  have h : (fun seed => (cachedDraw prepared rich seed).value.read) =
      (fun seed => if rich then i.realRichSample seed else i.realPoorSample seed) :=
    funext (cachedDraw_value prepared rich)
  apply ProbabilityMeasure.toMeasure_injective
  unfold cachedLaw
  simp only [ProbabilityMeasure.toMeasure_map,h]
  cases rich
  · exact i.realPoorSample_law
  · exact i.realRichSample_law

/-- Separate exact-uniform inputs produce the independent whole-allocation
product, retaining the within-player coupling. -/
theorem cachedDraw_product_law {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) :
    Measure.map (Prod.map (fun seed => (cachedDraw prepared true seed).value.read)
      (fun seed => (cachedDraw prepared false seed).value.read))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (cachedLaw prepared true : Measure (Allocation n)).prod
        (cachedLaw prepared false : Measure (Allocation n)) := by
  rw [← Measure.map_prod_map _ _ (cachedDraw_measurable prepared true) (cachedDraw_measurable prepared false)]
  rfl

theorem cachedDraw_equilibrium {n : ℕ} {i : RationalPRGOriginalInput n}
    (prepared : RealPRGInputExecution.Prepared i) :
    regret i.realValues (i.a : ℝ) (cachedLaw prepared true) (cachedLaw prepared false) = 0 ∧
      regret i.realValues (i.b : ℝ) (cachedLaw prepared false) (cachedLaw prepared true) = 0 ∧
      expected i.realValues (cachedLaw prepared true) (cachedLaw prepared false) = 1 - (i.normalizedInput.b : ℝ) / 2 ∧
      expected i.realValues (cachedLaw prepared false) (cachedLaw prepared true) = (i.normalizedInput.b : ℝ) / 2 := by
  rw [cachedLaw_state,cachedLaw_state]
  exact i.realEquilibrium

/-- A single request includes actual original-data preparation, followed by
the cached draw. Preparation may also be performed once for repeated draws. -/
noncomputable def originalDrawCached {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  let prepared := RealPRGInputExecution.prepare i values hV availableRich availablePoor hA hB
  join prepared (cachedDraw prepared.value rich seed)

theorem originalDrawCached_value {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).value.read =
      if rich then i.realRichSample seed else i.realPoorSample seed := cachedDraw_value _ _ _

theorem originalDrawCached_cost {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).cost ≤ 253 * n + 428240 := by
  have hp := RealPRGInputExecution.prepare_cost i values hV availableRich availablePoor hA hB
  have hd := cachedDraw_cost (RealPRGInputExecution.prepare i values hV availableRich availablePoor hA hB).value rich seed
  rw [originalDrawCached,join_cost]
  omega

theorem originalDrawCached_contract {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) (hs : realGroupSeedValid seed.2) :
    (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).cost ≤ 253 * values.data.size + 428240 ∧
      (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).value.data.size = values.data.size ∧
      FullBudget (if rich then (i.a : ℝ) else (i.b : ℝ))
        (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).value.read ∧
      Feasible (if rich then (i.a : ℝ) else (i.b : ℝ))
        (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).value.read := by
  have hf : FullBudget (if rich then (i.a : ℝ) else (i.b : ℝ))
      (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).value.read :=
    cachedDraw_fullBudget _ _ _ hs
  refine ⟨?_,?_,hf,fullBudget_feasible hf⟩
  · rw [values.size]
    exact originalDrawCached_cost _ _ _ _ _ _ _ _ _
  · rw [(originalDrawCached i values hV availableRich availablePoor hA hB rich seed).value.size,values.size]

/-- Recognition is charged before preparation and drawing. The proof inputs
identify a promised request; the guard is still executed from its stored data. -/
noncomputable def checkedOriginalDraw {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) : Run (Option (FixedArrayTable n ℝ)) :=
  let tested := RealPRGInputExecution.recognize values availableRich availablePoor
  join tested (if tested.value then
    let drawn := originalDrawCached i values hV availableRich availablePoor hA hB rich seed
    join (⟨(),[.control]⟩ : Run Unit) (join drawn ⟨some drawn.value,[.control]⟩)
    else ⟨none,[.control]⟩)

theorem checkedOriginalDraw_value {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    (checkedOriginalDraw i values hV availableRich availablePoor hA hB rich seed).value =
      some (originalDrawCached i values hV availableRich availablePoor hA hB rich seed).value := by
  simp only [checkedOriginalDraw,join_value,RealPRGInputExecution.recognize_original i values hV
    availableRich availablePoor hA hB,ite_true]

theorem checkedOriginalDraw_read {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    Option.map FixedArrayTable.read
      (checkedOriginalDraw i values hV availableRich availablePoor hA hB rich seed).value =
        some (if rich then i.realRichSample seed else i.realPoorSample seed) := by
  rw [checkedOriginalDraw_value]
  simp only [Option.map_some,originalDrawCached_value]

theorem checkedOriginalDraw_cost {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    (checkedOriginalDraw i values hV availableRich availablePoor hA hB rich seed).cost ≤
      273 * values.data.size + 428272 := by
  have ht := RealPRGInputExecution.recognize_cost values availableRich availablePoor
  have hd := originalDrawCached_cost i values hV availableRich availablePoor hA hB rich seed
  have hSize := values.size
  unfold checkedOriginalDraw
  rw [join_cost]
  split
  · rw [join_cost,join_cost]
    change _ + (1 + (_ + 1)) ≤ _
    omega
  · change _ + 1 ≤ _
    omega

theorem checkedOriginalDraw_feasible {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) (hs : realGroupSeedValid seed.2)
    (row : FixedArrayTable n ℝ)
    (hRow : (checkedOriginalDraw i values hV availableRich availablePoor hA hB rich seed).value = some row) :
    FullBudget (if rich then (i.a : ℝ) else (i.b : ℝ)) row.read ∧
      Feasible (if rich then (i.a : ℝ) else (i.b : ℝ)) row.read := by
  rw [checkedOriginalDraw_value] at hRow
  cases Option.some.inj hRow
  exact (originalDrawCached_contract i values hV availableRich availablePoor hA hB rich seed hs).2.2

/-- Mathematical readback of the checked stored output. On every promised
request the default is unreachable, as `checkedOriginalDraw_value` proves. -/
noncomputable def checkedSample {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) : Allocation n :=
  (Option.map FixedArrayTable.read
    (checkedOriginalDraw i values hV availableRich availablePoor hA hB rich seed).value).getD 0

theorem checkedSample_value {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) (seed : RealLottoSeed n) :
    checkedSample i values hV availableRich availablePoor hA hB rich seed =
      if rich then i.realRichSample seed else i.realPoorSample seed := by
  unfold checkedSample
  rw [checkedOriginalDraw_read]
  rfl

theorem checkedSample_measurable {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) : Measurable (checkedSample i values hV availableRich availablePoor hA hB rich) := by
  have h : checkedSample i values hV availableRich availablePoor hA hB rich =
      (fun seed => if rich then i.realRichSample seed else i.realPoorSample seed) :=
    funext (checkedSample_value i values hV availableRich availablePoor hA hB rich)
  rw [h]
  cases rich
  · exact i.realPoorSample_measurable
  · exact i.realRichSample_measurable

theorem checkedSample_law {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ))
    (rich : Bool) :
    Measure.map (checkedSample i values hV availableRich availablePoor hA hB rich)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
      (if rich then (i.realRichLaw : Measure (Allocation n)) else (i.realPoorLaw : Measure (Allocation n))) := by
  have h : checkedSample i values hV availableRich availablePoor hA hB rich =
      (fun seed => if rich then i.realRichSample seed else i.realPoorSample seed) :=
    funext (checkedSample_value i values hV availableRich availablePoor hA hB rich)
  rw [h]
  cases rich
  · exact i.realPoorSample_law
  · exact i.realRichSample_law

theorem checkedSample_product_law {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    Measure.map (Prod.map (checkedSample i values hV availableRich availablePoor hA hB true)
      (checkedSample i values hV availableRich availablePoor hA hB false))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (i.realRichLaw : Measure (Allocation n)).prod (i.realPoorLaw : Measure (Allocation n)) := by
  rw [← Measure.map_prod_map _ _ (checkedSample_measurable i values hV availableRich availablePoor hA hB true)
    (checkedSample_measurable i values hV availableRich availablePoor hA hB false),checkedSample_law,checkedSample_law]
  rfl

end Blotto.RealPRGGlobalExecution
