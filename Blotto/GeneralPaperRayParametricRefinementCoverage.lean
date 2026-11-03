import Blotto.GeneralPaperSourceCrossingRefinementRates

/-! Erased coverage of the refinements actually reached by the priced
parametric recursion and final budget stage. Logical batch properties are
instantiated on actual returned prefixes; no runtime trace or callback
oracle is added. Failure branches contain only previously executed calls. -/
namespace Blotto.GeneralPaperRayParametricRefinementCoverage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def recursion {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (Batch : ℚ → ℚ → List ℚ → Prop) : List (Field K) → ℚ → ℚ → Prop
  | [],_,_ => True
  | field::rest,lo,hi =>
    recursion model W matrix x w S h beta Batch rest lo hi ∧
      match (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
      | none => True
      | some previous => Batch previous.bracket.lower previous.bracket.upper
          (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous.table).1

theorem recursion_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (Batch : ℚ → ℚ → List ℚ → Prop)
    (hBatch : ∀ lo hi points,0≤lo → lo≤hi → hi≤1 → RationalHeight lo (width D E m X V P) →
      RationalHeight hi (width D E m X V P) → points.length≤(S+1)*(K*K) →
      (∀ t∈points,RationalHeight t (width D E m X V P)) → Batch lo hi points)
    (fields : List (Field K)) (hLen : fields.length≤m)
    (hf : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X V f)
    (lo hi : ℚ) (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    recursion model W matrix x w S h beta Batch fields lo hi := by
  induction fields with
  | nil => trivial
  | cons field rest ih =>
    have hRest : ∀ f∈rest,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := fun f ht => hf f (List.mem_cons_of_mem _ ht)
    have hRestLen : rest.length≤m := by simp only [List.length_cons] at hLen; omega
    refine ⟨ih hRestLen hRest,?_⟩
    cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
    | none => trivial
    | some previous =>
      dsimp only
      let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
      have hNative : GeneralPaperRayParametricDP.run query S rest lo hi=some previous :=
        (GeneralPaperParametricRunBits.data model W matrix x w S h beta rest lo hi).symm.trans hp
      have hHeight := GeneralPaperRayParametricRunSize.bracket hD hE query rest lo hi hRestLen hRest hl hh previous hNative
      have hInside := GeneralPaperRayBracketContainment.run query rest lo hi ho previous hNative
      have hTable := GeneralPaperRayAffineDPSize.run D E X V S query rest lo hi hRest previous hNative
      apply hBatch _ _ _ (hLo.trans hInside.1) hInside.2.1 (hInside.2.2.trans hHi) hHeight.1 hHeight.2
      · rw [GeneralPaperNativeAffinePrices.crossings_data]
        exact GeneralPaperRayAffineScoreStep.crossings_length field previous.table
      · intro t ht
        rw [GeneralPaperNativeAffinePrices.crossings_data] at ht
        exact stage_roots hD hE (show rest.length+1≤m from hLen) field previous.table (hf field List.mem_cons_self) hTable t ht

def high {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta lo hi : ℚ) (Batch : ℚ → ℚ → List ℚ → Prop) : Prop :=
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  recursion model W matrix x w S h beta Batch fields lo hi ∧
    match (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
    | none => True
    | some out => Batch out.bracket.lower out.bracket.upper (GeneralPaperBudgetCrossingPrice.run model.rat W out.table h beta).1

theorem recursion_mono {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (Batch Other : ℚ → ℚ → List ℚ → Prop)
    (hImp : ∀ lo hi points,Batch lo hi points → Other lo hi points) (fields : List (Field K)) (lo hi : ℚ)
    (hc : recursion model W matrix x w S h beta Batch fields lo hi) : recursion model W matrix x w S h beta Other fields lo hi := by
  induction fields with
  | nil => trivial
  | cons field rest ih =>
    rcases hc with ⟨hRest,hCurrent⟩
    refine ⟨ih hRest,?_⟩
    cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta rest lo hi).1 with
    | none => trivial
    | some previous =>
      rw [hp] at hCurrent
      exact hImp _ _ _ hCurrent

theorem high_mono {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (Batch Other : ℚ → ℚ → List ℚ → Prop)
    (hImp : ∀ lo hi points,Batch lo hi points → Other lo hi points) (lo hi : ℚ)
    (hc : high model W matrix x w S h beta lo hi Batch) : high model W matrix x w S h beta lo hi Other := by
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  rcases hc with ⟨hRest,hFinal⟩
  change (match (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
    | none => True
    | some out => Batch out.bracket.lower out.bracket.upper (GeneralPaperBudgetCrossingPrice.run model.rat W out.table h beta).1) at hFinal
  refine ⟨recursion_mono model W matrix x w S h beta Batch Other hImp fields lo hi hRest,?_⟩
  cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
  | none => trivial
  | some out =>
    rw [hp] at hFinal
    exact hImp _ _ _ hFinal

theorem high_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E) (hK : 0<K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a)) (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a))
    (S h : ℕ) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta)
    (Batch : ℚ → ℚ → List ℚ → Prop)
    (hBatch : ∀ lo hi points,0≤lo → lo≤hi → hi≤1 → RationalHeight lo (width D E m X V P) →
      RationalHeight hi (width D E m X V P) → points.length≤(S+1)*(K*K) →
      (∀ t∈points,RationalHeight t (width D E m X V P)) → Batch lo hi points)
    (lo hi : ℚ) (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    high model W matrix x w S h beta lo hi Batch := by
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  have hFields : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := by
    dsimp only [fields]
    rw [GeneralPaperAffineInputPrice.data]
    exact GeneralPaperRayAnchorBound.fields D E X V matrix x w hx hw
  have hLen : fields.length=m := by dsimp only [fields]; rw [GeneralPaperAffineInputPrice.data,GeneralPaperRayAffineScoreInput.fields_length]
  refine ⟨recursion_bounded model W D E X V P hD hE matrix x w S h beta Batch hBatch fields hLen.le hFields lo hi hLo ho hHi hl hh,?_⟩
  cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
  | none => trivial
  | some out =>
    dsimp only
    have hNative : GeneralPaperRayParametricDP.run query S fields lo hi=some out :=
      (GeneralPaperParametricRunBits.data model W matrix x w S h beta fields lo hi).symm.trans hp
    have hHeight := GeneralPaperRayParametricRunSize.bracket hD hE query fields lo hi hLen.le hFields hl hh out hNative
    have hInside := GeneralPaperRayBracketContainment.run query fields lo hi ho out hNative
    have hTable := GeneralPaperRayAffineDPSize.run D E X V S query fields lo hi hFields out hNative
    rw [hLen] at hTable
    apply hBatch _ _ _ (hLo.trans hInside.1) hInside.2.1 (hInside.2.2.trans hHi) hHeight.1 hHeight.2
    · have hc : S+1≤(S+1)*(K*K) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hK)
      rw [GeneralPaperBudgetCrossingPrice.data]
      exact (GeneralPaperRayBudgetCrossings.batch_length out.table h beta).trans hc
    · intro t ht
      rw [GeneralPaperBudgetCrossingPrice.data] at ht
      exact budget_roots hD hE le_rfl out.table hTable h beta hb t ht

end Blotto.GeneralPaperRayParametricRefinementCoverage
