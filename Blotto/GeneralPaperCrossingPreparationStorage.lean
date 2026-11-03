import Blotto.GeneralPaperListReferenceConstructionStorage

/-! All native crossing-array preparation phases: filter, selected sort,
deduplication and every materialization prefix. Original/intermediate lists,
the returned array and actual wrapper counters remain conservatively owned
together. Batch generation and the search/refinement caller are separate. -/
namespace Blotto.GeneralPaperCrossingPreparationStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def filtered (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : List ℚ×ℕ :=
  GeneralPaperPricedCrossingPasses.filterRun model.rat W lo hi points
def input (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : List ℚ := lo::hi::(filtered model W lo hi points).1
def sorted (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : List ℚ×ℕ :=
  GeneralPaperPricedSort.run (GeneralPaperPricedCrossingPasses.leRun model.rat) W (input model W lo hi points)
def distinct (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : List ℚ×ℕ :=
  GeneralPaperPricedCrossingPasses.uniqueRun model.rat W (sorted model W lo hi points).1

structure Facts (model : RationalCostModel) (W P n : ℕ) (lo hi : ℚ) (points : List ℚ) : Prop where
  filtered_length : (filtered model W lo hi points).1.length≤n+2
  filtered_word : ∀ t∈(filtered model W lo hi points).1,rationalWordWidth t≤P
  input_length : (input model W lo hi points).length≤n+2
  input_word : ∀ t∈input model W lo hi points,rationalWordWidth t≤P
  sorted_length : (sorted model W lo hi points).1.length≤n+2
  sorted_word : ∀ t∈(sorted model W lo hi points).1,rationalWordWidth t≤P
  distinct_length : (distinct model W lo hi points).1.length≤n+2
  distinct_word : ∀ t∈(distinct model W lo hi points).1,rationalWordWidth t≤P

theorem facts (model : RationalCostModel) (W P n : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hn : points.length≤n) (hl : rationalWordWidth lo≤P) (hh : rationalWordWidth hi≤P)
    (hp : ∀ t∈points,rationalWordWidth t≤P) : Facts model W P n lo hi points := by
  have hFLen : (filtered model W lo hi points).1.length≤n := by
    unfold filtered
    rw [GeneralPaperPricedCrossingPasses.filter_data]
    exact (List.length_filter_le _ _).trans hn
  have hFWord : ∀ t∈(filtered model W lo hi points).1,rationalWordWidth t≤P := by
    intro t ht
    rw [filtered,GeneralPaperPricedCrossingPasses.filter_data] at ht
    exact hp t (List.mem_filter.mp ht).1
  have hILen : (input model W lo hi points).length≤n+2 := by unfold input; simp only [List.length_cons]; omega
  have hIWord : ∀ t∈input model W lo hi points,rationalWordWidth t≤P := by
    intro t ht
    rcases List.mem_cons.mp ht with he|ht
    · rw [he]; exact hl
    · rcases List.mem_cons.mp ht with he|ht
      · rw [he]; exact hh
      · exact hFWord t ht
  have hSLen : (sorted model W lo hi points).1.length≤n+2 := by unfold sorted; rw [GeneralPaperPricedSort.length]; exact hILen
  have hSWord : ∀ t∈(sorted model W lo hi points).1,rationalWordWidth t≤P := by
    intro t ht
    exact hIWord t ((GeneralPaperPricedSort.mem _ W _ t).mp ht)
  have hDLen : (distinct model W lo hi points).1.length≤n+2 := by
    unfold distinct
    rw [GeneralPaperPricedCrossingPasses.unique_data]
    exact (GeneralPaperRaySortedCrossings.unique_sublist _).length_le.trans hSLen
  have hDWord : ∀ t∈(distinct model W lo hi points).1,rationalWordWidth t≤P := by
    intro t ht
    rw [distinct,GeneralPaperPricedCrossingPasses.unique_data] at ht
    exact hSWord t ((GeneralPaperRaySortedCrossings.unique_sublist _).subset ht)
  exact ⟨by omega,hFWord,hILen,hIWord,hSLen,hSWord,hDLen,hDWord⟩

def owners (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : ℕ :=
  let array := (GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points).1
  listFootprint W rationalWordWidth points+
    listFootprint W rationalWordWidth (filtered model W lo hi points).1+
    listFootprint W rationalWordWidth (input model W lo hi points)+
    listFootprint W rationalWordWidth (sorted model W lo hi points).1+
    listFootprint W rationalWordWidth (distinct model W lo hi points).1+
    GeneralPaperEncodedRationalRows.rowFootprint W array+rationalWordWidth lo+rationalWordWidth hi

def ownersProfile (W n R : ℕ) : ℕ := 5*((n+2)*(1+2*R+2*W)+32*W)+(n+2)*(1+2*R+W)+64*W+2*(1+2*R)

theorem owners_bound (model : RationalCostModel) (W n R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hn : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ t∈points,RationalHeight t R) :
    owners model W lo hi points≤ownersProfile W n R := by
  have hlw := rationalWordWidth_of_height hl
  have hhw := rationalWordWidth_of_height hh
  have hpw := fun t ht => rationalWordWidth_of_height (hp t ht)
  have hf := facts model W (1+2*R) n lo hi points hn hlw hhw hpw
  have list (xs : List ℚ) (hLen : xs.length≤n+2) (hWord : ∀ t∈xs,rationalWordWidth t≤1+2*R) :
      listFootprint W rationalWordWidth xs≤(n+2)*(1+2*R+2*W)+32*W :=
    (list_bound W (1+2*R) rationalWordWidth xs hWord).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  have hRaw := list points (by omega) hpw
  have hF := list _ hf.filtered_length hf.filtered_word
  have hI := list _ hf.input_length hf.input_word
  have hS := list _ hf.sorted_length hf.sorted_word
  have hD := list _ hf.distinct_length hf.distinct_word
  have hA := GeneralPaperEncodedRationalRows.row_bound W R (GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points).1 (by
    intro i
    rw [GeneralPaperPricedCrossingArray.data]
    exact GeneralPaperRayBracketSize.read_height lo hi points R hl hh hp i)
  have hLen := (GeneralPaperRaySortedCrossings.ordered_length lo hi points).trans (Nat.add_le_add_right hn 2)
  have hA' := hA.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  unfold owners ownersProfile
  dsimp only
  omega

def caller (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : ℕ :=
  let f := filtered model W lo hi points
  let s := sorted model W lo hi points
  let d := distinct model W lo hi points
  let pipeline := GeneralPaperPricedCrossingSort.run model.rat W lo hi points
  let material := PaperListReferenceArray.run (fun w => w) W pipeline.1
  let result := GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points
  fields W [points.length,f.1.length,(input model W lo hi points).length,s.1.length,d.1.length,pipeline.1.length,
    f.2,s.2,d.2,pipeline.2,material.2,result.2,f.2+s.2,f.2+s.2+d.2,pipeline.2+material.2,16*W,8*W]+256*W

def metadataCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+3+GeneralPaperPricedCrossingArray.profile n W (model.rat (1+2*R))
def callerProfile (model : RationalCostModel) (W n R : ℕ) : ℕ := 17*(natBits (metadataCap model W n R)+W)+288*W

theorem caller_bound (model : RationalCostModel) (W n R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hn : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ t∈points,RationalHeight t R)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+3)≤W) : caller model W lo hi points≤callerProfile model W n R := by
  let f := filtered model W lo hi points
  let s := sorted model W lo hi points
  let d := distinct model W lo hi points
  let pipeline := GeneralPaperPricedCrossingSort.run model.rat W lo hi points
  let material := PaperListReferenceArray.run (fun w => w) W pipeline.1
  let result := GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points
  have hf := facts model W (1+2*R) n lo hi points hn (rationalWordWidth_of_height hl) (rationalWordWidth_of_height hh)
    (fun t ht => rationalWordWidth_of_height (hp t ht))
  have hF : f.1.length≤n+2 := hf.filtered_length
  have hS : s.1.length≤n+2 := hf.sorted_length
  have hD : d.1.length≤n+2 := hf.distinct_length
  have hI := hf.input_length
  have hP : pipeline.1.length≤n+2 := (GeneralPaperPricedCrossingSort.length model.rat W lo hi points).trans (Nat.add_le_add_right hn 2)
  have hWork := (GeneralPaperPricedCrossingArray.bit_work model W R lo hi points hW
    ((binaryWordWidth_mono (Nat.add_le_add_right hn 3)).trans hIndex) hl hh hp).trans
      (GeneralPaperRayRefinementResidents.price_mono hn W (model.rat (1+2*R)))
  change result.2≤GeneralPaperPricedCrossingArray.profile n W (model.rat (1+2*R)) at hWork
  have hPipeline : pipeline.2=f.2+s.2+d.2+16*W := rfl
  have hShape : result.2=pipeline.2+material.2+8*W := rfl
  have hFields := fields_bound W (natBits (metadataCap model W n R))
    [points.length,f.1.length,(input model W lo hi points).length,s.1.length,d.1.length,pipeline.1.length,
      f.2,s.2,d.2,pipeline.2,material.2,result.2,f.2+s.2,f.2+s.2+d.2,pipeline.2+material.2,16*W,8*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤17*(natBits (metadataCap model W n R)+W)+32*W at hFields
  change GeneralPaperEncodedScalarStorage.fields W [points.length,f.1.length,(input model W lo hi points).length,s.1.length,d.1.length,pipeline.1.length,
    f.2,s.2,d.2,pipeline.2,material.2,result.2,f.2+s.2,f.2+s.2+d.2,pipeline.2+material.2,16*W,8*W]+256*W≤_
  unfold callerProfile
  omega

inductive Phase where
  | filter
  | sort
  | deduplicate
  | materialize (used : ℕ)
  | returned

def localWindow (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : Phase → ℕ
  | .filter => GeneralPaperCrossingPassStorage.filterWindow model W lo hi points
  | .sort => GeneralPaperSelectedSortStorage.window model W rationalWordWidth (GeneralPaperPricedCrossingPasses.leRun model.rat) (input model W lo hi points)
  | .deduplicate => GeneralPaperCrossingPassStorage.uniqueWindow model W (sorted model W lo hi points).1
  | .materialize used => GeneralPaperListReferenceConstructionStorage.window W used rationalWordWidth (distinct model W lo hi points).1
  | .returned => 0

def window (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) (phase : Phase) : ℕ :=
  owners model W lo hi points+caller model W lo hi points+localWindow model W lo hi points phase

def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  ownersProfile W n R+callerProfile model W n R+
    GeneralPaperCrossingPassStorage.profile W (1+2*R) (model.rat (1+2*R)) (n+2)+
    GeneralPaperSelectedSortStorage.profile model W (1+2*R) (model.rat (1+2*R)) (n+2)+
    GeneralPaperListReferenceConstructionStorage.profile W (1+2*R) (n+2)

theorem all_phases (model : RationalCostModel) (W n R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hn : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ t∈points,RationalHeight t R)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+3)≤W) (phase : Phase) :
    window model W lo hi points phase≤profile model W n R := by
  have hR : 1≤R := by
    by_contra h
    have hz : R=0 := by omega
    have hd := hl.2
    rw [hz,pow_zero] at hd
    have hp := lo.den_pos
    omega
  have hlw := rationalWordWidth_of_height hl
  have hhw := rationalWordWidth_of_height hh
  have hpw := fun t ht => rationalWordWidth_of_height (hp t ht)
  have hf := facts model W (1+2*R) n lo hi points hn hlw hhw hpw
  have hO := owners_bound model W n R lo hi points hn hl hh hp
  have hC := caller_bound model W n R lo hi points hn hl hh hp hW hIndex
  have hZero : rationalWordWidth (0:ℚ)≤1+2*R := rationalWordWidth_of_height
    ((show RationalHeight (0:ℚ) 1 by norm_num [RationalHeight]).mono hR)
  have hLocal : localWindow model W lo hi points phase≤
      GeneralPaperCrossingPassStorage.profile W (1+2*R) (model.rat (1+2*R)) (n+2)+
      GeneralPaperSelectedSortStorage.profile model W (1+2*R) (model.rat (1+2*R)) (n+2)+
      GeneralPaperListReferenceConstructionStorage.profile W (1+2*R) (n+2) := by
    cases phase with
    | filter =>
      have h := GeneralPaperCrossingPassStorage.filter_window model W (1+2*R) (model.rat (1+2*R)) (n+2) lo hi points (by omega) hlw hhw hpw le_rfl
      change GeneralPaperCrossingPassStorage.filterWindow model W lo hi points≤_
      omega
    | sort =>
      have h := GeneralPaperSelectedSortStorage.bounded model W (1+2*R) (model.rat (1+2*R)) (n+2) rationalWordWidth
        (GeneralPaperPricedCrossingPasses.leRun model.rat) (input model W lo hi points) hf.input_length hf.input_word
        (fun a ha b hb => GeneralPaperPricedCrossingPasses.le_work model.rat model.monotone a b (1+2*R) (hf.input_word a ha) (hf.input_word b hb))
      change GeneralPaperSelectedSortStorage.window model W rationalWordWidth (GeneralPaperPricedCrossingPasses.leRun model.rat) (input model W lo hi points)≤_
      omega
    | deduplicate =>
      have h := GeneralPaperCrossingPassStorage.unique_window model W (1+2*R) (model.rat (1+2*R)) (n+2) _ hf.sorted_length hf.sorted_word hZero le_rfl
      change GeneralPaperCrossingPassStorage.uniqueWindow model W (sorted model W lo hi points).1≤_
      omega
    | materialize used =>
      have h := GeneralPaperListReferenceConstructionStorage.bounded W (1+2*R) (n+2) used rationalWordWidth _ hf.distinct_length hf.distinct_word hW
        (by simpa only [Nat.add_assoc] using hIndex)
      change GeneralPaperListReferenceConstructionStorage.window W used rationalWordWidth (distinct model W lo hi points).1≤_
      omega
    | returned => change 0≤_; omega
  exact (Nat.add_le_add (Nat.add_le_add hO hC) hLocal).trans_eq (by unfold profile; ring)

theorem stage_batch {S K m : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : GeneralPaperRayAffineScoreStep.Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous)
    (lo hi : ℚ) (hl : RationalHeight lo (GeneralPaperRayUniformSize.width D E m X V P))
    (hh : RationalHeight hi (GeneralPaperRayUniformSize.width D E m X V P))
    (hW : 1≤W) (hIndex : binaryWordWidth ((S+1)*(K*K)+3)≤W) (phase : Phase) :
    window model W lo hi (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1 phase≤
      profile model W ((S+1)*(K*K)) (GeneralPaperRayUniformSize.width D E m X V P) := by
  have hLen : (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1.length≤(S+1)*(K*K) := by
    rw [GeneralPaperNativeAffinePrices.crossings_data]
    exact GeneralPaperRayAffineScoreStep.crossings_length field previous
  apply all_phases model W _ _ lo hi _ hLen hl hh _ hW hIndex phase
  intro q hq
  rw [GeneralPaperNativeAffinePrices.crossings_data] at hq
  exact GeneralPaperRayUniformSize.stage_roots hD hE hn field previous hf hp q hq

theorem budget_batch {S K m : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : GeneralPaperRayAffineScoreStep.Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table)
    (h : ℕ) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (GeneralPaperRayUniformSize.width D E m X V P))
    (hh : RationalHeight hi (GeneralPaperRayUniformSize.width D E m X V P))
    (hW : 1≤W) (hIndex : binaryWordWidth (S+4)≤W) (phase : Phase) :
    window model W lo hi (GeneralPaperBudgetCrossingPrice.run model.rat W table h beta).1 phase≤
      profile model W (S+1) (GeneralPaperRayUniformSize.width D E m X V P) := by
  have hLen : (GeneralPaperBudgetCrossingPrice.run model.rat W table h beta).1.length≤S+1 := by
    rw [GeneralPaperBudgetCrossingPrice.data]
    exact GeneralPaperRayBudgetCrossings.batch_length table h beta
  apply all_phases model W _ _ lo hi _ hLen hl hh _ hW (by simpa only [Nat.add_assoc] using hIndex) phase
  intro q hq
  rw [GeneralPaperBudgetCrossingPrice.data] at hq
  exact GeneralPaperRayUniformSize.budget_roots hD hE hn table hp h beta hb q hq

end Blotto.GeneralPaperCrossingPreparationStorage
