import Blotto.GeneralPaperCatalogueOptimizerBudget
import Blotto.GeneralPaperAdaptiveLossBounds

/-! Prepare both literal code catalogues, both native optimizer caches and
the four-family field plans from the same epoch summaries. The state domain
below retains these constructed plans, whose option arrays are nonempty.
This supplies an inhabited domain for the actual adaptive row selectors.
-/
namespace Blotto.GeneralPaperCatalogueEpochCache
open GeneralPaperCodeAlphabet
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Cache (m k : ℕ) where
  alphabet : Alphabet
  p : FixedArrayTable m (Summary k)
  q : FixedArrayTable m (Summary k)
  lambda : FixedArrayTable m (Summary k)
  mu : FixedArrayTable m (Summary k)
  candidate : GeneralPaperCatalogueOptimizer.Ready m k
  response : GeneralPaperCatalogueOptimizer.Ready m k
  plans : FixedArrayTable m (GeneralPaperEpochFieldPlan.Plan k)
  candidate_spec : candidate=GeneralPaperCatalogueOptimizer.prepare alphabet false k lambda
  response_spec : response=GeneralPaperCatalogueOptimizer.prepare alphabet true k mu
  plans_spec : plans=FixedArrayTable.ofFn (fun j => GeneralPaperEpochFieldPlan.prepare k (8*alphabet.C)
    (p.read j) (q.read j) (lambda.read j) (mu.read j) (candidate.data.codes.read j) (response.data.codes.read j))

def prepare {m : ℕ} (a : Alphabet) (k : ℕ) (p q lambda mu : FixedArrayTable m (Summary k)) : Cache m k :=
  let candidate := GeneralPaperCatalogueOptimizer.prepare a false k lambda
  let response := GeneralPaperCatalogueOptimizer.prepare a true k mu
  let plans := FixedArrayTable.ofFn (fun j => GeneralPaperEpochFieldPlan.prepare k (8*a.C)
    (p.read j) (q.read j) (lambda.read j) (mu.read j) (candidate.data.codes.read j) (response.data.codes.read j))
  ⟨a,p,q,lambda,mu,candidate,response,plans,rfl,rfl,rfl⟩

theorem plan_read {m k : ℕ} (cache : Cache m k) (j : Fin m) :
    cache.plans.read j=GeneralPaperEpochFieldPlan.prepare k (8*cache.alphabet.C)
      (cache.p.read j) (cache.q.read j) (cache.lambda.read j) (cache.mu.read j)
      (cache.candidate.data.codes.read j) (cache.response.data.codes.read j) := by
  rw [cache.plans_spec,FixedArrayTable.read_ofFn]

theorem candidate_count {m k : ℕ} (cache : Cache m k) (j : Fin m) :
    (cache.plans.read j).candidateCount=(GeneralPaperSourceParameters.prepare k).summarySize+2 := by
  rw [plan_read]
  rfl

theorem response_count {m k : ℕ} (cache : Cache m k) (j : Fin m) :
    (cache.plans.read j).responseCount=(GeneralPaperSourceParameters.prepare k).summarySize+2 := by
  rw [plan_read]
  rfl

theorem candidate_options_data {m k : ℕ} (cache : Cache m k) (j : Fin m) :
    (cache.plans.read j).candidateOptions.data=(cache.candidate.data.codes.read j).data := by
  rw [plan_read]
  rfl

theorem response_options_data {m k : ℕ} (cache : Cache m k) (j : Fin m) :
    (cache.plans.read j).responseOptions.data=(cache.response.data.codes.read j).data := by
  rw [plan_read]
  rfl

theorem constructed {m k : ℕ} (cache : Cache m k) (j : Fin m) : GeneralPaperEpochFieldPlan.Constructed (cache.plans.read j) := by
  rw [plan_read]
  exact GeneralPaperEpochFieldPlan.prepare_constructed _ _ _ _ _ _ _ _

structure State {m k : ℕ} (cache : Cache m k) where
  fields : GeneralPaperAdaptiveEpoch.Fields m k
  plan_spec : ∀ j, (fields.read j).plan=cache.plans.read j

def initial {m k : ℕ} (cache : Cache m k) : State cache :=
  ⟨GeneralPaperAdaptiveEpoch.initial cache.plans,by intro j; rw [GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn]; rfl⟩

theorem unrestricted_selector_empty (m k : ℕ) (hm : 0<m) : ¬Nonempty (GeneralPaperAdaptiveEpoch.Selector m k) := by
  rintro ⟨select⟩
  let summary : Summary k := FixedArrayTable.ofFn (fun _ => 0)
  let empty : FixedArrayTable 0 ℕ := FixedArrayTable.ofFn Fin.elim0
  let plan := GeneralPaperEpochFieldPlan.prepare k 0 summary summary summary summary empty empty
  let fields : GeneralPaperAdaptiveEpoch.Fields m k := FixedArrayTable.ofFn (fun _ => GeneralPaperEpochFieldState.initial plan)
  let before := GeneralPaperAdaptiveEpoch.snapshots (GeneralPaperPreparedPowers.prepare 0 k) fields
  have he := (select fields before).candidateValid ⟨0,hm⟩
  have hz : (fields.read ⟨0,hm⟩).plan.candidateCount=0 := by
    simp only [fields,FixedArrayTable.read_ofFn]
    rfl
  rw [hz] at he
  omega

end Blotto.GeneralPaperCatalogueEpochCache
