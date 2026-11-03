import Blotto.PlayerSpecificFiniteResourceContract
import Blotto.TerminalLottoGrouping

/-! Executable next-fit grouping over original algebraic lengths. Each
group retains its member list and one cached reduced total. -/
namespace Blotto.PlayerSpecificAlgebraicGrouping
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Group (N : ℕ) where
  members : List (Fin N)
  total : Data

def packAux {N : ℕ} (model : RationalCostModel) (root : Candidate) (length : Fin N → Data) (B : ℚ) :
    List (Fin N) → Data → List (Fin N) → List (Group N)
  | current,s,[] => [⟨current.reverse,s⟩]
  | current,s,k::rest =>
      let combined:=PlayerSpecificAlgebraicField.plus root.polynomial s (length k)
      if PlayerSpecificAlgebraicPairStep.le model root combined [B] then
        packAux model root length B (k::current) combined rest
      else ⟨current.reverse,s⟩::packAux model root length B [k] (length k) rest

def run {N : ℕ} (model : RationalCostModel) (root : Candidate) (length : Fin N → Data) (B : ℚ) :
    List (Fin N) → List (Group N)
  | [] => []
  | k::rest => packAux model root length B [k] (length k) rest

theorem aux_members {N : ℕ} (model : RationalCostModel) (root : Candidate) (length : Fin N → Data) (B : ℚ)
    (current : List (Fin N)) (s : Data) (rest : List (Fin N))
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    (packAux model root length B current s rest).map Group.members=
      Blotto.packAux (fun k => realEvaluate (length k) x) B current (realEvaluate s x) rest := by
  induction rest generalizing current s with
  | nil => rfl
  | cons k rest ih =>
      have hc:=PlayerSpecificAlgebraicPairStep.le_correct model root
        (PlayerSpecificAlgebraicField.plus root.polynomial s (length k)) [B] hm hirr hv x hx
      rw [PlayerSpecificAlgebraicField.plus_value _ _ _ x hx.1] at hc
      have hB : realEvaluate [B] x=(B:ℝ) := by
        simp only [realEvaluate,List.foldr_cons,List.foldr_nil,mul_zero,add_zero]
      rw [hB] at hc
      unfold packAux Blotto.packAux
      dsimp only
      by_cases hfit : PlayerSpecificAlgebraicPairStep.le model root
          (PlayerSpecificAlgebraicField.plus root.polynomial s (length k)) [B]=true
      · rw [ite_eq_left hfit,ite_eq_left (hc.mp hfit),ih]
        rw [PlayerSpecificAlgebraicField.plus_value _ _ _ x hx.1]
      · rw [ite_eq_right hfit,ite_eq_right (fun h => hfit (hc.mpr h))]
        simp only [List.map_cons,ih]

theorem members {N : ℕ} (model : RationalCostModel) (root : Candidate) (length : Fin N → Data) (B : ℚ)
    (items : List (Fin N)) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    (run model root length B items).map Group.members=greedyGroups (fun k => realEvaluate (length k) x) B items := by
  cases items with
  | nil => rfl
  | cons k rest => exact aux_members model root length B [k] (length k) rest hm hirr hv x hx

def uniformItems {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) : List (Fin N) :=
  (List.finRange N).filter (fun k => PlayerSpecificAlgebraicField.equal p.parameters.root.polynomial (s.data.read k) (p.rows.read k).length)

theorem uniformItems_value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (x : ℝ) (hm : Normalized p.parameters.root.polynomial)
    (hirr : Irreducible (semantics p.parameters.root.polynomial)) (hx : realEvaluate p.parameters.root.polynomial x=0) :
    uniformItems p s=(List.finRange N).filter (fun k => decide (eval s x k=lengths p x k)) := by
  unfold uniformItems
  congr 1
  funext k
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact PlayerSpecificAlgebraicField.equal_value _ _ _ hm hirr x hx

end Blotto.PlayerSpecificAlgebraicGrouping
