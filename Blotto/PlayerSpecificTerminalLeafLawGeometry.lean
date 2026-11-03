import Blotto.PlayerSpecificLeafMapLaw
import Blotto.PlayerSpecificAlgebraicTerminalLeafZeros

/-! The actual cached grouping derives a proportional whole-law map
for the executing original-leaf sampler. Its partition is proof-only;
the runtime uses the already checked direct member writes. -/
namespace Blotto.PlayerSpecificTerminalLeafLawGeometry
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicGrouping
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ)
    (H K : ℕ) (x : ℝ) : Mixed N :=
  (fairBitLaw (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K)).map
    (fun bits => values (PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits) x)

theorem saturated_member {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (j : Fin N) (hj : eval s x j=lengths p x j) :
    ∃ g : Fin (prepare model p s B).groups.length,j ∈ ((prepare model p s B).groups.get g).members := by
  have he : j ∈ ((prepare model p s B).groups.map Group.members).flatten := by
    rw [PlayerSpecificAlgebraicTerminalGroupBounds.members_flatten model p s B x hc,
      uniformItems_value p s x hc.normalized hc.irreducible hc.root.1]
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    exact hj
  obtain ⟨members,hm,hjmem⟩ := List.mem_flatten.mp he
  obtain ⟨group,hgroup,hgm⟩ := List.mem_map.mp hm
  obtain ⟨g,hg⟩ := List.mem_iff_get.mp hgroup
  refine ⟨g,?_⟩
  rw [hg,hgm]
  exact hjmem

theorem geometry {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hsize : ∀ k,PlayerSpecificPolynomialHeights.HasHeight (p.rows.read k).length T) (H K : ℕ) :
    let g := prepare RationalCostModel.schoolbook p s B
    ∃ G : ProportionalGroups N g.groups.length,
      (∀ j,G.length j=lengths p x j) ∧
      (∀ h j,j ∈ G.members h ↔ j ∈ (g.groups.get h).members) ∧
      (∀ h,G.total h=realEvaluate (g.groups.get h).total x) ∧
      (∀ k,g.fractional=some k → ∀ h,k ∉ G.members h) ∧
      law p s B H K x=(PlayerSpecificTerminalCoreBranchLaws.law p.parameters
        (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g) H K x).map
          (PlayerSpecificAlgebraicLeafValues.point G g.fractional) := by
  let model := RationalCostModel.schoolbook
  let g := prepare model p s B
  let L := fun j => (p.rows.read j).length
  have hm0 : p.parameters.root.polynomial ≠ [] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hn := PlayerSpecificAlgebraicTerminalGroupBounds.members_nodup model p s B x hc
  have hcache := groups_cached model p s B hc.normalized hm0 hc.lengths
  have hcached := PlayerSpecificAlgebraicTerminalGroupBounds.cached_bounds model p s B x hc hs hB hL hb hmass hend T hsize
  have hpos : ∀ h ∈ g.groups,0 < realEvaluate h.total x := fun h hh => (hcached h hh).2.2.2.1
  let G := PlayerSpecificAlgebraicLeafPartition.partition p.parameters.root L g.groups x (fun j => (hL j).1) hn hcache hpos
  have hp : ∀ k,g.fractional=some k → ∀ h : Fin g.groups.length,k ∉ (g.groups.get h).members :=
    fun k hk h => PlayerSpecificAlgebraicTerminalLeafGroups.fractional_not_member model p s B x hc hs hend k hk h
  refine ⟨G,fun _ => rfl,?_,?_,?_,?_⟩
  · intro h j
    exact PlayerSpecificAlgebraicLeafPartition.mem_partition p.parameters.root L g.groups x (fun j => (hL j).1) hn hcache hpos h j
  · intro h
    exact PlayerSpecificAlgebraicLeafPartition.total_value p.parameters.root L g.groups x (fun j => (hL j).1) hn hcache hpos h
  · intro k hk h hm
    exact hp k hk h ((PlayerSpecificAlgebraicLeafPartition.mem_partition p.parameters.root L g.groups x
      (fun j => (hL j).1) hn hcache hpos h k).mp hm)
  · apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (fun bits => values (PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits) x) _=
      Measure.map (PlayerSpecificAlgebraicLeafValues.point G g.fractional)
        (Measure.map (fun bits => values (PlayerSpecificAlgebraicTerminalCoreDraw.draw p.parameters
          (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g) H K bits) x)
            (fairBitLaw (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) : Measure _))
    rw [Measure.map_map (PlayerSpecificLeafMapLaw.measurable_point G g.fractional) (measurable_of_countable _)]
    congr 1
    funext bits
    exact PlayerSpecificAlgebraicLeafValues.mixed_value p.parameters.root L g.groups x (fun j => (hL j).1) hn hcache hpos
      hc.normalized hc.irreducible hc.root.1 g.fractional hp _

end Blotto.PlayerSpecificTerminalLeafLawGeometry
