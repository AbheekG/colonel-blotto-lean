import Blotto.PlayerSpecificFiniteCellSearch

/-! Completeness of the executing finite-bit cell search, including all
irrational interior roots and exact rational breakpoints. -/
namespace Blotto.PlayerSpecificFiniteCellCompleteness
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates PlayerSpecificSturmVariations
open PlayerSpecificFiniteCellSearch
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem interior_exists (model : RationalCostModel) (c : Cell) (b : ℚ) (hb : b≠0)
    (hp : semantics (cubic c.state.coefficients b)≠0) (x : ℝ)
    (hroot : PlayerSpecificCubic.cubic (castCell c).state.coefficients (b:ℝ) x=0)
    (hx : PlayerSpecificCellCandidates.Interior (castCell c) x)
    (hpass : PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) x) :
    ∃ r,interior model c b=some r := by
  have horiginal : realEvaluate (cubic c.state.coefficients b) x=0 := by
    rw [PlayerSpecificRationalIntervals.cubic_value]
    exact hroot
  obtain ⟨r,hr,hcontains⟩:=(PlayerSpecificCandidateContract.actual_contract model _ hp (by rfl)).2.2.1 x horiginal
  have he:=PlayerSpecificCandidateContract.each model _ hp (by rfl) r hr
  have hrootr : realEvaluate r.polynomial x=0 := (he.2.2.2 x hcontains).mpr horiginal
  have ht: PlayerSpecificAlgebraicCandidateTest.run model c r=true :=
    (PlayerSpecificAlgebraicCandidateTest.correct model _ hp (by rfl) r hr c b hb x ⟨hrootr,hcontains⟩).mpr ⟨hx,hpass⟩
  cases hfind : interior model c b with
  | some q => exact ⟨q,rfl⟩
  | none =>
    have hn:=List.find?_eq_none.mp hfind r hr
    exact (hn ht).elim

theorem breakpoint_exists (c : Cell) (b : ℚ) (x : ℝ)
    (hx : x∈PlayerSpecificCellCandidates.breakpoints (castCell c) (b:ℝ))
    (hpass : PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) x) :
    ∃ r,PlayerSpecificRationalBreakpoint.run c b=some r := by
  classical
  cases hu : c.upper with
  | none =>
    have huR : (castCell c).upper=none := by simp only [castCell,hu,Option.map_none]
    simp only [PlayerSpecificCellCandidates.breakpoints,huR,List.not_mem_nil] at hx
  | some q =>
    have huR : (castCell c).upper=some (q:ℝ) := by simp only [castCell,hu,Option.map_some]
    have hxq : x=(q:ℝ) := by
      rw [PlayerSpecificCellCandidates.breakpoints,huR] at hx
      by_cases ht : (0:ℝ)<(q:ℝ) ∧ (castCell c).lower≤(q:ℝ) ∧
          PlayerSpecificCubic.cubic (castCell c).state.coefficients (b:ℝ) (q:ℝ)=0
      · simp only [ht] at hx
        exact List.mem_singleton.mp hx
      · simp only [ht,ite_false] at hx
        cases hx
    subst x
    exact ⟨PlayerSpecificRationalBreakpoint.candidate q,
      (PlayerSpecificRationalBreakpoint.correct c b q).mpr ⟨hx,(PlayerSpecificRationalBreakpoint.passes_cast c b q).mpr hpass⟩⟩

theorem complete (model : RationalCostModel) (c : Cell) (b : ℚ) (hb : b≠0)
    (hp : semantics (cubic c.state.coefficients b)≠0) (x : ℝ)
    (hx : x∈PlayerSpecificCellCandidates.candidates (castCell c) (b:ℝ))
    (hpass : PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) x) :
    ∃ r,PlayerSpecificFiniteCellSearch.run model c b=some r := by
  classical
  cases hi : interior model c b with
  | some r => exact ⟨r,by rw [PlayerSpecificFiniteCellSearch.run,hi]⟩
  | none =>
    rcases List.mem_append.mp hx with hinside | hbreak
    · have hfilter:=List.mem_filter.mp hinside
      have hroot:=(PlayerSpecificPolynomial.root_membership (castCell c).state.coefficients (b:ℝ) x
        (polynomial_nonzero c b hp)).mp hfilter.1
      obtain ⟨r,hr⟩:=interior_exists model c b hb hp x hroot (of_decide_eq_true hfilter.2) hpass
      rw [hi] at hr
      cases hr
    · obtain ⟨r,hr⟩:=breakpoint_exists c b x hbreak hpass
      exact ⟨r,by rw [PlayerSpecificFiniteCellSearch.run,hi]; exact hr⟩

end Blotto.PlayerSpecificFiniteCellCompleteness
