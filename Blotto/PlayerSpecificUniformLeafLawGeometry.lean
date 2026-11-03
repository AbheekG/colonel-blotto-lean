import Blotto.PlayerSpecificFourSpecHybrid

/-! The proof-only proportional partition is fixed across all H. Its
lengths and actual native member lists determine it uniquely. -/
namespace Blotto.PlayerSpecificUniformLeafLawGeometry
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificAlgebraicResourceState
open PlayerSpecificAlgebraicTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem ext_data {N m : ℕ} (G F : ProportionalGroups N m) (hl : G.length=F.length) (hm : G.members=F.members) : G=F := by
  cases G
  cases F
  simp_all

theorem geometry {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hsize : ∀ k,PlayerSpecificPolynomialHeights.HasHeight (p.rows.read k).length T) (K : ℕ) :
    let g := prepare RationalCostModel.schoolbook p s B
    ∃ G : ProportionalGroups N g.groups.length,
      (∀ j,G.length j=lengths p x j) ∧
      (∀ h j,j ∈ G.members h ↔ j ∈ (g.groups.get h).members) ∧
      (∀ h,G.total h=realEvaluate (g.groups.get h).total x) ∧
      (∀ k,g.fractional=some k → ∀ h,k ∉ G.members h) ∧
      ∀ H,PlayerSpecificTerminalLeafLawGeometry.law p s B H K x=(PlayerSpecificTerminalCoreBranchLaws.law p.parameters
        (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g) H K x).map
          (PlayerSpecificAlgebraicLeafValues.point G g.fractional) := by
  obtain ⟨G,hGlen,hGmem,hGtotal,hGpivot,_⟩ := PlayerSpecificTerminalLeafLawGeometry.geometry p s B x hc hs hB hL hb hmass hend T hsize 0 K
  refine ⟨G,hGlen,hGmem,hGtotal,hGpivot,?_⟩
  intro H
  obtain ⟨F,hFlen,hFmem,_,_,hlaw⟩ := PlayerSpecificTerminalLeafLawGeometry.geometry p s B x hc hs hB hL hb hmass hend T hsize H K
  have hlength : F.length=G.length := funext (fun j => (hFlen j).trans (hGlen j).symm)
  have hmembers : F.members=G.members := by
    funext h
    apply Finset.ext
    intro j
    exact (hFmem h j).trans (hGmem h j).symm
  have he : F=G := ext_data F G hlength hmembers
  subst F
  exact hlaw

end Blotto.PlayerSpecificUniformLeafLawGeometry
