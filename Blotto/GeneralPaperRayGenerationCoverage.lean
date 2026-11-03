import Blotto.GeneralPaperSourceCrossingStreamRates

/-! Coverage of actual native generation/refinement stage calls. Pair and
budget properties see the actual returned affine table and bracket. Matrix
score caps, processed-field invariants and bracket/root bounds are derived
on those native returns, including failure paths. -/
namespace Blotto.GeneralPaperRayGenerationCoverage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

theorem field_scores {m K : ℕ} (W S : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hs : ∀ j l,((matrix.read j).read l).1≤S) (x w : Variable m K → ℚ) (field : Field K)
    (hf : field∈(GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1) : ∀ l,(field.read l).1≤S := by
  rw [GeneralPaperAffineInputPrice.data] at hf
  unfold GeneralPaperRayAffineScoreInput.fields at hf
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
  intro l
  simpa only [FixedArrayTable.read_ofFn,GeneralPaperRayQueryWork.scores] using hs j l

def recursion {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ)
    (Pair : Field K → GeneralPaperRayParametricDP.Output S K → Prop) : List (Field K) → ℚ → ℚ → Prop
  | [],_,_ => True
  | field::rest,lo,hi => recursion model W matrix x w S h beta Pair rest lo hi ∧
      match (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
      | none => True
      | some previous => Pair field previous

theorem recursion_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ)
    (Pair : Field K → GeneralPaperRayParametricDP.Output S K → Prop)
    (hPair : ∀ n field (out : GeneralPaperRayParametricDP.Output S K),n+1≤m →
      GeneralPaperRayAffineDPSize.FieldBounded D E X V field → GeneralPaperRayAffineDPSize.TableBounded D E X V n out.table →
      (∀ l,(field.read l).1≤S) → 0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 →
      RationalHeight out.bracket.lower (width D E m X V P) → RationalHeight out.bracket.upper (width D E m X V P) → Pair field out)
    (fields : List (Field K)) (hLen : fields.length≤m) (hf : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X V f)
    (hScores : ∀ f∈fields,∀ l,(f.read l).1≤S)
    (lo hi : ℚ) (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    recursion model W matrix x w S h beta Pair fields lo hi := by
  induction fields with
  | nil => trivial
  | cons field rest ih =>
    have hRest : ∀ f∈rest,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := fun f ht => hf f (List.mem_cons_of_mem _ ht)
    have hRestLen : rest.length≤m := by simp only [List.length_cons] at hLen; omega
    refine ⟨ih hRestLen hRest (fun f ht => hScores f (List.mem_cons_of_mem _ ht)),?_⟩
    cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
    | none => trivial
    | some previous =>
      let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
      have hNative : GeneralPaperRayParametricDP.run query S rest lo hi=some previous :=
        (GeneralPaperParametricRunBits.data model W matrix x w S h beta rest lo hi).symm.trans hp
      have hHeight := GeneralPaperRayParametricRunSize.bracket hD hE query rest lo hi hRestLen hRest hl hh previous hNative
      have hInside := GeneralPaperRayBracketContainment.run query rest lo hi ho previous hNative
      have hTable := GeneralPaperRayAffineDPSize.run D E X V S query rest lo hi hRest previous hNative
      exact hPair rest.length field previous hLen (hf field List.mem_cons_self) hTable (hScores field List.mem_cons_self)
        (hLo.trans hInside.1) hInside.2.1 (hInside.2.2.trans hHi) hHeight.1 hHeight.2

def high {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (S h : ℕ) (beta lo hi : ℚ)
    (Pair : Field K → GeneralPaperRayParametricDP.Output S K → Prop) (Budget : GeneralPaperRayParametricDP.Output S K → Prop) : Prop :=
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  recursion model W matrix x w S h beta Pair fields lo hi ∧
    match (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
    | none => True
    | some out => Budget out

theorem high_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a)) (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a))
    (S h : ℕ) (beta : ℚ) (hScores : ∀ j l,((matrix.read j).read l).1≤S)
    (Pair : Field K → GeneralPaperRayParametricDP.Output S K → Prop) (Budget : GeneralPaperRayParametricDP.Output S K → Prop)
    (hPair : ∀ n field (out : GeneralPaperRayParametricDP.Output S K),n+1≤m →
      GeneralPaperRayAffineDPSize.FieldBounded D E X V field → GeneralPaperRayAffineDPSize.TableBounded D E X V n out.table →
      (∀ l,(field.read l).1≤S) → 0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 →
      RationalHeight out.bracket.lower (width D E m X V P) → RationalHeight out.bracket.upper (width D E m X V P) → Pair field out)
    (hBudget : ∀ out : GeneralPaperRayParametricDP.Output S K,GeneralPaperRayAffineDPSize.TableBounded D E X V m out.table →
      0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 →
      RationalHeight out.bracket.lower (width D E m X V P) → RationalHeight out.bracket.upper (width D E m X V P) → Budget out)
    (lo hi : ℚ) (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    high model W matrix x w S h beta lo hi Pair Budget := by
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  have hFields : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := by
    dsimp only [fields]
    rw [GeneralPaperAffineInputPrice.data]
    exact GeneralPaperRayAnchorBound.fields D E X V matrix x w hx hw
  have hLen : fields.length=m := by dsimp only [fields]; rw [GeneralPaperAffineInputPrice.data,GeneralPaperRayAffineScoreInput.fields_length]
  refine ⟨recursion_bounded model W D E X V P hD hE matrix x w S h beta Pair hPair fields hLen.le hFields
    (fun field hf => field_scores W S matrix hScores x w field hf) lo hi hLo ho hHi hl hh,?_⟩
  cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
  | none => trivial
  | some out =>
    have hNative : GeneralPaperRayParametricDP.run query S fields lo hi=some out :=
      (GeneralPaperParametricRunBits.data model W matrix x w S h beta fields lo hi).symm.trans hp
    have hHeight := GeneralPaperRayParametricRunSize.bracket hD hE query fields lo hi hLen.le hFields hl hh out hNative
    have hInside := GeneralPaperRayBracketContainment.run query fields lo hi ho out hNative
    have hTable := GeneralPaperRayAffineDPSize.run D E X V S query fields lo hi hFields out hNative
    rw [hLen] at hTable
    exact hBudget out hTable (hLo.trans hInside.1) hInside.2.1 (hInside.2.2.trans hHi) hHeight.1 hHeight.2

theorem recursion_mono {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (Pair Other : Field K → GeneralPaperRayParametricDP.Output S K → Prop)
    (hImp : ∀ field out,Pair field out → Other field out) (fields : List (Field K)) (lo hi : ℚ)
    (hc : recursion model W matrix x w S h beta Pair fields lo hi) :
    recursion model W matrix x w S h beta Other fields lo hi := by
  induction fields with
  | nil => trivial
  | cons field rest ih =>
    rcases hc with ⟨hRest,hCurrent⟩
    refine ⟨ih hRest,?_⟩
    cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
    | none => trivial
    | some previous =>
      rw [hp] at hCurrent
      exact hImp field previous hCurrent

theorem high_mono {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (Pair OtherPair : Field K → GeneralPaperRayParametricDP.Output S K → Prop)
    (Budget OtherBudget : GeneralPaperRayParametricDP.Output S K → Prop)
    (hPair : ∀ field out,Pair field out → OtherPair field out)
    (hBudget : ∀ out,Budget out → OtherBudget out) (lo hi : ℚ)
    (hc : high model W matrix x w S h beta lo hi Pair Budget) :
    high model W matrix x w S h beta lo hi OtherPair OtherBudget := by
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  rcases hc with ⟨hRest,hFinal⟩
  change (match (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
    | none => True
    | some out => Budget out) at hFinal
  refine ⟨recursion_mono model W matrix x w S h beta Pair OtherPair hPair fields lo hi hRest,?_⟩
  cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
  | none => trivial
  | some out =>
    rw [hp] at hFinal
    exact hBudget out hFinal

end Blotto.GeneralPaperRayGenerationCoverage
