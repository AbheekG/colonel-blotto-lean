import Blotto.PlayerSpecificAlgebraicActive

/-! Computable resource arrays and maintained active indices. Real
interpretation and invariant witnesses are proof-only; no real value or
selection oracle is supplied to the executing state operations. -/
namespace Blotto.PlayerSpecificAlgebraicResourceState
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure State (N : ℕ) where
  data : FixedArrayTable N Data
  active : List (Fin N)

noncomputable def eval {N : ℕ} (s : State N) (x : ℝ) : Allocation N := fun j => realEvaluate (s.data.read j) x
noncomputable def lengths {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) : Allocation N :=
  fun j => realEvaluate (p.rows.read j).length x

structure Valid {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) (s : State N) : Prop where
  nodup : s.active.Nodup
  membership : ∀ j,j∈s.active ↔ Fractional (lengths p x) (eval s x) j
  reduced : ∀ j,Reduced p.parameters.root.polynomial (s.data.read j)

noncomputable def interpret {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) (s : State N)
    (h : Valid p x s) : ActiveResourceList (lengths p x) :=
  ⟨eval s x,s.active,h.nodup,h.membership⟩

theorem length_eq_card {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) (s : State N)
    (h : Valid p x s) : s.active.length=(fractionalSet (lengths p x) (eval s x)).card :=
  (interpret p x s h).length_eq_card

def start {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (firstPlayer : Bool) : State N :=
  let data:=FixedArrayTable.ofFn (PlayerSpecificInitialLineageBound.means p firstPlayer)
  ⟨data,(List.finRange N).filter (fun j => PlayerSpecificAlgebraicActive.run model p.parameters.root (p.rows.read j).length (data.read j))⟩

def update {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (i j : Fin N) (tail : List (Fin N)) (a b : Data) : State N :=
  let data:=(s.data.write i a).write j b
  ⟨data,[i,j].filter (fun k => PlayerSpecificAlgebraicActive.run model p.parameters.root (p.rows.read k).length (data.read k))++tail⟩

theorem start_read {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (firstPlayer : Bool) (j : Fin N) :
    (start model p firstPlayer).data.read j=PlayerSpecificInitialLineageBound.means p firstPlayer j :=
  FixedArrayTable.read_ofFn _ j

theorem start_valid {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (firstPlayer : Bool)
    (hm : Normalized p.parameters.root.polynomial) (hirr : Irreducible (semantics p.parameters.root.polynomial))
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x)
    (hr : ∀ j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p firstPlayer j)) :
    Valid p x (start model p firstPlayer) := by
  constructor
  · exact (List.nodup_finRange N).filter _
  · intro j
    simp only [start,List.mem_filter,List.mem_finRange,true_and]
    exact PlayerSpecificAlgebraicActive.correct model p.parameters.root _ _ hm hirr hv x hx
  · intro j
    rw [start_read]
    exact hr j

theorem eval_update {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (i j : Fin N) (tail : List (Fin N)) (a b : Data) (hij : i≠j) (x : ℝ)
    (hb : realEvaluate b x=eval s x i+eval s x j-realEvaluate a x) :
    eval (update model p s i j tail a b) x=Blotto.updatePair (eval s x) i j (realEvaluate a x) := by
  funext k
  by_cases hkj : k=j
  · subst k
    rw [Blotto.updatePair_j]
    simpa only [eval,update,FixedArrayTable.read_write,ite_true] using hb
  · by_cases hki : k=i
    · subst k
      rw [Blotto.updatePair_i _ hij]
      simp only [eval,update,FixedArrayTable.read_write,ite_eq_right hij,ite_true]
    · rw [Blotto.updatePair_other _ hki hkj]
      simp only [eval,update,FixedArrayTable.read_write,ite_eq_right hkj,ite_eq_right hki]

end Blotto.PlayerSpecificAlgebraicResourceState
