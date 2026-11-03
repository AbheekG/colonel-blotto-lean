import Blotto.PlayerSpecificFiniteCellCompleteness

/-! Actual finite-bit recognition scans the rational cells and retains a
computed irreducible root representation. These are functional correctness
joins; complete sweep/test source-cost and size joins remain separate. -/
namespace Blotto.PlayerSpecificFiniteRecognition
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 3000000

def scan (model : RationalCostModel) (b : ℚ) : List Cell → Option (Cell×Candidate)
  | [] => none
  | c::cs =>
    match PlayerSpecificFiniteCellSearch.run model c b with
    | some r => some (c,r)
    | none => scan model b cs
def run {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) : Option (Cell×Candidate) :=
  scan model i.budget (PlayerSpecificRationalIntervals.run i)

theorem scan_sound (model : RationalCostModel) (b : ℚ) (cells : List Cell) (c : Cell) (r : Candidate)
    (hr : scan model b cells=some (c,r)) : c∈cells ∧ PlayerSpecificFiniteCellSearch.run model c b=some r := by
  induction cells with
  | nil => cases hr
  | cons d ds ih =>
    rw [scan] at hr
    split at hr
    · rename_i chosen hchosen
      have he:=Option.some.inj hr
      have hc : d=c := congrArg Prod.fst he
      have hrepr : chosen=r := congrArg Prod.snd he
      subst d
      subst chosen
      exact ⟨List.mem_cons_self,hchosen⟩
    · have ht:=ih hr
      exact ⟨List.mem_cons_of_mem d ht.1,ht.2⟩

theorem scan_complete (model : RationalCostModel) (b : ℚ) (cells : List Cell) (c : Cell) (r : Candidate)
    (hc : c∈cells) (hr : PlayerSpecificFiniteCellSearch.run model c b=some r) :
    ∃ chosen,scan model b cells=some chosen := by
  induction cells with
  | nil => cases hc
  | cons d ds ih =>
    rw [scan]
    split
    · rename_i repr _
      exact ⟨(d,repr),rfl⟩
    · rename_i hn
      have htail : c∈ds := by
        rcases List.mem_cons.mp hc with he | hmem
        · subst c
          rw [hn] at hr
          cases hr
        · exact hmem
      exact ih htail

theorem sound {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) (c : Cell) (r : Candidate)
    (hr : run model i=some (c,r)) :
    PlayerSpecificFiniteCellSearch.Good c i.budget r ∧
      ∀ x : ℝ,PlayerSpecificSturmVariations.realEvaluate r.polynomial x=0 → r.interval.Contains x →
        PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) x
          (PlayerSpecificCubic.candidateScale (castCell c).state.coefficients (i.budget:ℝ) x) := by
  have hs:=scan_sound model i.budget (PlayerSpecificRationalIntervals.run i) c r hr
  have hgood:=PlayerSpecificFiniteCellSearch.sound model c i.budget i.budget_pos.ne'
    (PlayerSpecificRationalIntervals.cubic_nonzero i c hs.1) r hs.2
  obtain ⟨low,high,hperm,hfit⟩:=PlayerSpecificRationalIntervals.fits i c hs.1
  refine ⟨hgood,?_⟩
  obtain ⟨y,hy,_⟩:=hgood.2.2.2.2
  obtain ⟨z,hz,hzunique⟩:=hgood.2.2.2.1
  intro x hx hxin
  have hxeq : x=y := (hzunique x ⟨hx,hxin⟩).trans (hzunique y ⟨hy.1,hy.2.1⟩).symm
  subst x
  exact PlayerSpecificRecognition.cell_sound i.valuesA.values i.valuesB.values low high hperm (castCell c) hfit
    (i.budget:ℝ) y (by exact_mod_cast i.budget_pos) hy.2.2.1 hy.2.2.2

end Blotto.PlayerSpecificFiniteRecognition
