import Blotto.GeneralPaperRaySearchProbeTrace
import Blotto.GeneralPaperHighSearchBits

/-! Erased exact query lists of the actual priced parametric recursion and
final budget refinement. Branches use actual native returned prefixes.
Every queried rational lies in the original bracket with one uniform root
height. Trace length is not used as a working-space bound. -/
namespace Blotto.GeneralPaperRayParametricProbeTrace
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def recursion {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) : List (Field K) → ℚ → ℚ → List ℚ
  | [],_,_ => []
  | field::rest,lo,hi =>
    let earlier := recursion model W matrix x w S h beta rest lo hi
    match (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
    | none => earlier
    | some previous => earlier++GeneralPaperRaySearchProbeTrace.refinement model.rat (fun w => w) W
        (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) previous.bracket.lower previous.bracket.upper
        (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous.table).1

theorem recursion_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (fields : List (Field K)) (hLen : fields.length≤m)
    (hf : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X V f)
    (lo hi : ℚ) (hOrder : lo≤hi) (hl : RationalHeight lo (width D E m X V P))
    (hh : RationalHeight hi (width D E m X V P)) (t : ℚ)
    (ht : t∈recursion model W matrix x w S h beta fields lo hi) :
    lo≤t ∧ t≤hi ∧ RationalHeight t (width D E m X V P) := by
  induction fields with
  | nil => simp only [recursion,List.not_mem_nil] at ht
  | cons field rest ih =>
    have hRest : ∀ f∈rest,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := fun f hf' => hf f (List.mem_cons_of_mem _ hf')
    have hRestLen : rest.length≤m := by simp only [List.length_cons] at hLen; omega
    rw [recursion] at ht
    cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
    | none =>
      simp only [hp] at ht
      exact ih hRestLen hRest ht
    | some previous =>
      simp only [hp,List.mem_append] at ht
      rcases ht with ht|ht
      · exact ih hRestLen hRest ht
      · let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
        have hNative : GeneralPaperRayParametricDP.run query S rest lo hi=some previous :=
          (GeneralPaperParametricRunBits.data model W matrix x w S h beta rest lo hi).symm.trans hp
        have hHeight := GeneralPaperRayParametricRunSize.bracket hD hE query rest lo hi hRestLen hRest hl hh previous hNative
        have hInside := GeneralPaperRayBracketContainment.run query rest lo hi hOrder previous hNative
        have hTable := GeneralPaperRayAffineDPSize.run D E X V S query rest lo hi hRest previous hNative
        have hn : rest.length+1≤m := hLen
        have hRoots : ∀ q∈(GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous.table).1,
            RationalHeight q (width D E m X V P) := by
          intro q hq
          rw [GeneralPaperNativeAffinePrices.crossings_data] at hq
          exact stage_roots hD hE hn field previous.table (hf field List.mem_cons_self) hTable q hq
        have hBound := GeneralPaperRaySearchProbeTrace.bounded model.rat (fun w => w) W _
          (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) previous.bracket.lower previous.bracket.upper
          (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous.table).1
          hInside.2.1 hHeight.1 hHeight.2 hRoots t ht
        exact ⟨hInside.1.trans hBound.1,hBound.2.1.trans hInside.2.2,hBound.2.2⟩

def high {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta lo hi : ℚ) : List ℚ :=
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  let earlier := recursion model W matrix x w S h beta fields lo hi
  match (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
  | none => earlier
  | some out => earlier++GeneralPaperRaySearchProbeTrace.refinement model.rat (fun w => w) W
      (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) out.bracket.lower out.bracket.upper
      (GeneralPaperBudgetCrossingPrice.run model.rat W out.table h beta).1

theorem high_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a)) (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a))
    (S h : ℕ) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta)
    (lo hi : ℚ) (hOrder : lo≤hi) (hl : RationalHeight lo (width D E m X V P))
    (hh : RationalHeight hi (width D E m X V P)) (t : ℚ) (ht : t∈high model W matrix x w S h beta lo hi) :
    lo≤t ∧ t≤hi ∧ RationalHeight t (width D E m X V P) := by
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  have hFields : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := by
    dsimp only [fields]
    rw [GeneralPaperAffineInputPrice.data]
    exact GeneralPaperRayAnchorBound.fields D E X V matrix x w hx hw
  have hLen : fields.length=m := by
    dsimp only [fields]
    rw [GeneralPaperAffineInputPrice.data,GeneralPaperRayAffineScoreInput.fields_length]
  rw [high] at ht
  change t∈match (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
    | none => recursion model W matrix x w S h beta fields lo hi
    | some out => recursion model W matrix x w S h beta fields lo hi++
        GeneralPaperRaySearchProbeTrace.refinement model.rat (fun w => w) W
          (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) out.bracket.lower out.bracket.upper
          (GeneralPaperBudgetCrossingPrice.run model.rat W out.table h beta).1 at ht
  cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
  | none =>
    simp only [hp] at ht
    exact recursion_bounded model W D E X V P hD hE matrix x w S h beta fields hLen.le hFields lo hi hOrder hl hh t ht
  | some out =>
    simp only [hp,List.mem_append] at ht
    rcases ht with ht|ht
    · exact recursion_bounded model W D E X V P hD hE matrix x w S h beta fields hLen.le hFields lo hi hOrder hl hh t ht
    · have hNative : GeneralPaperRayParametricDP.run query S fields lo hi=some out :=
        (GeneralPaperParametricRunBits.data model W matrix x w S h beta fields lo hi).symm.trans hp
      have hHeight := GeneralPaperRayParametricRunSize.bracket hD hE query fields lo hi hLen.le hFields hl hh out hNative
      have hInside := GeneralPaperRayBracketContainment.run query fields lo hi hOrder out hNative
      have hTable := GeneralPaperRayAffineDPSize.run D E X V S query fields lo hi hFields out hNative
      rw [hLen] at hTable
      have hRoots : ∀ q∈(GeneralPaperBudgetCrossingPrice.run model.rat W out.table h beta).1,
          RationalHeight q (width D E m X V P) := by
        intro q hq
        rw [GeneralPaperBudgetCrossingPrice.data] at hq
        exact budget_roots hD hE le_rfl out.table hTable h beta hb q hq
      have hBound := GeneralPaperRaySearchProbeTrace.bounded model.rat (fun w => w) W _
        (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) out.bracket.lower out.bracket.upper
        (GeneralPaperBudgetCrossingPrice.run model.rat W out.table h beta).1 hInside.2.1 hHeight.1 hHeight.2 hRoots t ht
      exact ⟨hInside.1.trans hBound.1,hBound.2.1.trans hInside.2.2,hBound.2.2⟩

end Blotto.GeneralPaperRayParametricProbeTrace
