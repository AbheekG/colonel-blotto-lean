import Blotto.PlayerSpecificFactorRealRoots

/-! Computed irreducible candidate representations. Each original isolating
interval is matched against the actual removed rational factors. If none
matches, the residual factor retains its unique real root. -/
namespace Blotto.PlayerSpecificAlgebraicCandidates
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Candidate where
  polynomial : Data
  interval : Interval

def inside (node : Interval) (q : ℚ) : Bool := decide (node.lo<q ∧ q≤node.hi)
def lookup (factors : Data) (node : Interval) : Option ℚ := factors.find? (inside node)
def select (factors residual : Data) (node : Interval) : Candidate :=
  ⟨match lookup factors node with
    | some q => PlayerSpecificLinearFactor.linear q
    | none => residual,node⟩
def run (p : Data) : List Candidate :=
  let factors:=PlayerSpecificRationalFactors.factor p
  (PlayerSpecificRootIsolation.run p).map (select factors.1 factors.2)

theorem select_interval (factors residual : Data) (node : Interval) : (select factors residual node).interval=node := by
  cases lookup factors node <;> rfl

theorem lookup_some (factors : Data) (node : Interval) (q : ℚ) (hq : lookup factors node=some q) :
    q∈factors ∧ node.Contains (q:ℝ) := by
  have hm:=List.mem_of_find?_eq_some hq
  have hi:=List.find?_some hq
  have hb : node.lo<q ∧ q≤node.hi := of_decide_eq_true hi
  refine ⟨hm,?_,?_⟩
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

theorem lookup_none (factors : Data) (node : Interval) (hn : lookup factors node=none)
    (x : ℝ) (hx : node.Contains x) : ∀ q∈factors,(q:ℝ)≠x := by
  intro q hq he
  have hnq:=List.find?_eq_none.mp hn q hq
  have hb : node.lo<q ∧ q≤node.hi := by
    rw [←he] at hx
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  exact hnq (by simpa only [inside,decide_eq_true_eq] using hb)

theorem linear_real (q : ℚ) (x : ℝ) : realEvaluate (PlayerSpecificLinearFactor.linear q) x=x-(q:ℝ) := by
  rw [←realEvaluate_semantics,PlayerSpecificLinearFactor.linear_semantics,Polynomial.eval₂_sub,
    Polynomial.eval₂_X,Polynomial.eval₂_C]
  rfl

theorem select_contract (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (node : Interval)
    (hnode : node∈PlayerSpecificRootIsolation.run p) :
    let candidate:=select (PlayerSpecificRationalFactors.factor p).1 (PlayerSpecificRationalFactors.factor p).2 node
    Irreducible (semantics candidate.polynomial) ∧ candidate.polynomial.length≤4 ∧
      (∃! x : ℝ,realEvaluate candidate.polynomial x=0 ∧ node.Contains x) ∧
      (∀ x : ℝ,node.Contains x → (realEvaluate candidate.polynomial x=0 ↔ realEvaluate p x=0)) := by
  have hf:=PlayerSpecificRationalFactors.factor_contract p hp hlen
  have hu:=PlayerSpecificRootIsolation.unique_roots p hp hlen node hnode
  cases hlookup : lookup (PlayerSpecificRationalFactors.factor p).1 node with
  | none =>
    have htransfer : ∀ x : ℝ,node.Contains x → realEvaluate p x=0 →
        realEvaluate (PlayerSpecificRationalFactors.factor p).2 x=0 := by
      intro x hx hroot
      exact PlayerSpecificFactorRealRoots.residual_root p hp hlen x hroot (lookup_none _ node hlookup x hx)
    obtain ⟨x,hx,hunique⟩:=hu
    have hres:=htransfer x hx.2 hx.1
    have hdegree:=PlayerSpecificFactorRealRoots.positive_degree _ hf.2.1 x hres
    simp only [select,hlookup]
    refine ⟨PlayerSpecificRationalFactors.residual_irreducible p hp hlen hdegree,
      hf.2.2.2.2.1.trans hlen,⟨x,⟨hres,hx.2⟩,?_⟩,?_⟩
    · intro y hy
      exact hunique y ⟨PlayerSpecificFactorRealRoots.original_root p hp hlen y hy.1,hy.2⟩
    · intro y hy
      exact ⟨PlayerSpecificFactorRealRoots.original_root p hp hlen y,htransfer y hy⟩
  | some q =>
    have hq:=lookup_some _ node q hlookup
    have hqroot:=hf.2.2.2.2.2.2 q hq.1
    have hqreal : realEvaluate p (q:ℝ)=0 := by rw [evaluate_cast,hqroot,Rat.cast_zero]
    have hsame : ∀ x : ℝ,realEvaluate p x=0 → node.Contains x → x=(q:ℝ) := by
      obtain ⟨y,hy,hunique⟩:=hu
      intro x hx hxin
      exact (hunique x ⟨hx,hxin⟩).trans (hunique (q:ℝ) ⟨hqreal,hq.2⟩).symm
    simp only [select,hlookup]
    refine ⟨PlayerSpecificLinearFactor.linear_irreducible q,by
      simp only [PlayerSpecificLinearFactor.linear,List.length_cons,List.length_nil]; decide,?_,?_⟩
    · refine ⟨(q:ℝ),⟨by rw [linear_real,sub_self],hq.2⟩,?_⟩
      intro x hx
      exact sub_eq_zero.mp ((linear_real q x).symm.trans hx.1)
    · intro x hxin
      constructor
      · intro hx
        have he:=sub_eq_zero.mp ((linear_real q x).symm.trans hx)
        simpa only [he] using hqreal
      · intro hx
        rw [linear_real,hsame x hx hxin,sub_self]

theorem length_bound (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) : (run p).length≤3 := by
  rw [run,List.length_map]
  exact PlayerSpecificRootIsolation.length_le_three p hp hlen

theorem covers (p : Data) (hp : semantics p≠0) (x : ℝ) (hroot : realEvaluate p x=0) :
    ∃ candidate∈run p,candidate.interval.Contains x := by
  obtain ⟨node,hnode,hx⟩:=PlayerSpecificRootIsolation.covers p hp x hroot
  exact ⟨select (PlayerSpecificRationalFactors.factor p).1 (PlayerSpecificRationalFactors.factor p).2 node,
    List.mem_map.mpr ⟨node,hnode,rfl⟩,hx⟩

end Blotto.PlayerSpecificAlgebraicCandidates
