import Blotto.GeneralPaperCatalogueOccurrenceHistory

/-! Ordered/bounded summary metadata transfers to the actual constructed
field plans. All candidate/response option validity is derived from native
catalogue execution, not added to the summary assumptions. The two signed
learners use one alphabet of twice the unsigned width.
-/
namespace Blotto.GeneralPaperCatalogueEpochMetadata
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 3500000

def width {m k : ℕ} (learner : Learner) (cache : Cache m k) : ℕ :=
  match learner with
  | .p | .q => 8*cache.alphabet.C
  | .lambda | .mu => 2*(8*cache.alphabet.C)

def height {m k : ℕ} (learner : Learner) (cache : Cache m k) : ℕ :=
  match learner with
  | .p | .q => cache.alphabet.lambda
  | .lambda | .mu => cache.alphabet.lambda+1

def Ordered {m k : ℕ} (cache : Cache m k) : Prop := ∀ learner j, Monotone (summary learner cache j).read

def CodesValid {m k : ℕ} (cache : Cache m k) : Prop := ∀ learner j r, (summary learner cache j).read r<width learner cache

theorem width_positive {m k : ℕ} (learner : Learner) (cache : Cache m k) : 0<width learner cache := by
  have hc := cache.alphabet.scalePositive
  cases learner <;> dsimp only [width] <;> omega

theorem width_power {m k : ℕ} (learner : Learner) (cache : Cache m k) : width learner cache=2^(height learner cache) := by
  have he := cache.alphabet.dyadic
  cases learner <;> dsimp only [width,height]
  · exact he
  · exact he
  · rw [pow_succ,←he]
    omega
  · rw [pow_succ,←he]
    omega

theorem height_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) : height learner cache≤cache.alphabet.lambda+1 := by
  cases learner <;> dsimp only [height] <;> omega

theorem field_alphabet {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) :
    (fieldAt run time j).plan.alphabet=8*cache.alphabet.C := by
  rw [field_plan,GeneralPaperCatalogueEpochCache.plan_read]
  rfl

theorem field_ordered {m k : ℕ} (cache : Cache m k) (hOrdered : Ordered cache) (j : Fin m) :
    GeneralPaperEpochFieldPlan.Ordered (cache.plans.read j) := by
  rw [GeneralPaperCatalogueEpochCache.plan_read]
  exact ⟨hOrdered .p j,hOrdered .q j,hOrdered .lambda j,hOrdered .mu j⟩

theorem field_codes {m k : ℕ} (cache : Cache m k) (hCodes : CodesValid cache) (j : Fin m) :
    GeneralPaperEpochFieldPlan.CodesValid (cache.plans.read j) := by
  rw [GeneralPaperCatalogueEpochCache.plan_read]
  refine ⟨hCodes .p j,hCodes .q j,hCodes .lambda j,hCodes .mu j,?_,?_⟩
  · intro r
    have he : cache.candidate.data=GeneralPaperCatalogueArrays.prepare cache.alphabet false k cache.lambda := by
      rw [cache.candidate_spec]
      rfl
    change (cache.candidate.data.codes.read j).read r<8*cache.alphabet.C
    rw [he]
    exact GeneralPaperCatalogueArrays.code_bound cache.alphabet false k cache.lambda j r
  · intro r
    have he : cache.response.data=GeneralPaperCatalogueArrays.prepare cache.alphabet true k cache.mu := by
      rw [cache.response_spec]
      rfl
    change (cache.response.data.codes.read j).read r<8*cache.alphabet.C
    rw [he]
    exact GeneralPaperCatalogueArrays.code_bound cache.alphabet true k cache.mu j r

end Blotto.GeneralPaperCatalogueEpochMetadata
