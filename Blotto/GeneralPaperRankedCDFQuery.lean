import Blotto.GeneralPaperRankCache

/-! Actual cached-rank queries and their reference CDF function. Exact
zero/one endpoints, monotonicity and unit bounds follow from constructed
ranks and native prefix arrays. The reference lookup is used in proofs;
runtime queries read the prebuilt rank cache.
-/
namespace Blotto.GeneralPaperRankedCDFQuery
open scoped BigOperators
open GeneralPaperSelectedRank
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem prefix_monotone {n : ℕ} (values : FixedArrayTable n ℕ) :
    Monotone (GeneralPaperEpochPrefixArray.build values).read := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  change (GeneralPaperEpochPrefixArray.build values).read ⟨a.val,by omega⟩≤
    (GeneralPaperEpochPrefixArray.build values).read ⟨b.val,by omega⟩
  rw [GeneralPaperEpochPrefixQuery.read_prefix values a.val (by omega),
    GeneralPaperEpochPrefixQuery.read_prefix values b.val (by omega)]
  apply Finset.sum_le_sum
  intro r _
  have hAB : a.val≤b.val := hab
  by_cases hR : r.val<a.val
  · simp only [hR,show r.val<b.val by omega,ite_true,le_refl]
  · simp only [hR,ite_false]
    exact Nat.zero_le _

def referenceCount (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (cut : ℕ) : ℕ :=
  (GeneralPaperEpochPrefixQuery.query k preparedPrefix (lookup k summary cut).position).quotient

def referenceValue (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (cut : ℕ) : ℚ :=
  GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
    (referenceCount k summary preparedPrefix cut)

def cached {m : ℕ} (k : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (ranks : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin m) :
    GeneralPaperBoundedQuotient.Result :=
  let result := GeneralPaperEpochPrefixQuery.query k preparedPrefix (ranks.read q)
  ⟨result.quotient,result.remainder,result.work+8⟩

theorem cached_count {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (cuts : FixedArrayTable m ℕ) (q : Fin m) :
    (cached k preparedPrefix (GeneralPaperRankCache.build k summary cuts).1 q).quotient=
      referenceCount k summary preparedPrefix (cuts.read q) := by
  unfold cached referenceCount
  rw [GeneralPaperRankCache.read_build]

theorem reference_count_bound (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (cut : ℕ) :
    referenceCount k summary (GeneralPaperEpochPrefixArray.build values) cut≤(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  (GeneralPaperEpochPrefixQuery.query_bounds k values (lookup k summary cut).position hTotal).1

theorem reference_bounds (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (cut : ℕ) :
    0≤referenceValue k summary (GeneralPaperEpochPrefixArray.build values) cut ∧
      referenceValue k summary (GeneralPaperEpochPrefixArray.build values) cut≤1 :=
  GeneralPaperRoundedLosses.component_bounds _ _ (GeneralPaperSourceParameters.mesh_positive k)
    (reference_count_bound k summary values hTotal cut)

theorem reference_count_monotone (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    Monotone (referenceCount k summary (GeneralPaperEpochPrefixArray.build values)) := by
  intro small large hCuts
  have hOrder := prefix_monotone values (lookup_monotone k summary hMono hCuts)
  have hPos : 0<(GeneralPaperEpochPrefixArray.build values).read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize) := by
    rw [GeneralPaperEpochPrefixQuery.read_total]
    exact hTotal
  exact GeneralPaperCDFMesh.evaluate_monotone _ _ _ _ _ hPos
    (GeneralPaperEpochPrefixQuery.read_le_total values (lookup k summary large).position) hOrder
    (GeneralPaperCDFMesh.selected_depth k)

theorem reference_monotone (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    Monotone (referenceValue k summary (GeneralPaperEpochPrefixArray.build values)) := by
  intro small large hCuts
  have he := reference_count_monotone k summary values hMono hTotal hCuts
  unfold referenceValue GeneralPaperRoundedLosses.component
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast he

theorem reference_count_zero (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    referenceCount k summary (GeneralPaperEpochPrefixArray.build values) 0=0 := by
  have hr : (lookup k summary 0).position=0 := by apply Fin.ext; exact lookup_zero k summary hMono
  have hPos : 0<(GeneralPaperEpochPrefixArray.build values).read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize) := by
    rw [GeneralPaperEpochPrefixQuery.read_total]
    exact hTotal
  unfold referenceCount GeneralPaperEpochPrefixQuery.query GeneralPaperCDFMesh.selected
  rw [hr,GeneralPaperEpochPrefixArray.read_zero]
  exact GeneralPaperCDFMesh.evaluate_zero _ _ _ hPos (GeneralPaperCDFMesh.selected_depth k)

theorem reference_count_full (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (cut : ℕ) (hAll : ∀ r, summary.read r<cut) :
    referenceCount k summary (GeneralPaperEpochPrefixArray.build values) cut=(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  have hr : (lookup k summary cut).position=Fin.last (GeneralPaperSourceParameters.prepare k).summarySize := by
    apply Fin.ext
    exact lookup_full k summary hMono cut hAll
  have hPos : 0<(GeneralPaperEpochPrefixArray.build values).read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize) := by
    rw [GeneralPaperEpochPrefixQuery.read_total]
    exact hTotal
  unfold referenceCount GeneralPaperEpochPrefixQuery.query GeneralPaperCDFMesh.selected
  rw [hr]
  exact GeneralPaperCDFMesh.evaluate_one _ _ _ hPos (GeneralPaperCDFMesh.selected_depth k)

theorem reference_zero (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    referenceValue k summary (GeneralPaperEpochPrefixArray.build values) 0=0 := by
  rw [referenceValue,reference_count_zero k summary values hMono hTotal]
  simp [GeneralPaperRoundedLosses.component]

theorem reference_full (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (cut : ℕ) (hAll : ∀ r, summary.read r<cut) :
    referenceValue k summary (GeneralPaperEpochPrefixArray.build values) cut=1 := by
  rw [referenceValue,reference_count_full k summary values hMono hTotal cut hAll]
  exact div_self (by exact_mod_cast ne_of_gt (GeneralPaperSourceParameters.mesh_positive k))

theorem cached_work {m : ℕ} (k : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (ranks : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin m) :
    (cached k preparedPrefix ranks q).work=12*(30+k)+42 := by
  unfold cached
  dsimp only
  rw [GeneralPaperEpochPrefixQuery.query_work]

end Blotto.GeneralPaperRankedCDFQuery
