import Blotto.PlayerSpecificTerminalLeafLawGeometry

/-! Every original coordinate of the actual reached terminal draw has
the required zero/uniform marginal approximation. Computed groups, core
validity, sizes, fractional quotient and direct output writes are joined. -/
namespace Blotto.PlayerSpecificTerminalLeafCDF
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicLeafAssignments
open PlayerSpecificTerminalLeafLawGeometry (law)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem zero_marginal {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hend : s.active.length ≤ 1) (hL : ∀ j,0 < lengths p x j)
    (j : Fin N) (hz : eval s x j=0) (H K : ℕ) :
    (marginal (law p s B H K x) j : Measure ℝ)=Measure.dirac 0 := by
  change Measure.map (fun y : Allocation N => y j) (Measure.map
    (fun bits => PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits) x)
      (fairBitLaw (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) : Measure _))=_
  rw [Measure.map_map (measurable_pi_apply j) (measurable_of_countable _)]
  have he : (fun y : Allocation N => y j) ∘
      (fun bits => PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits) x)=
        fun _ => (0:ℝ) := by
    funext bits
    change realEvaluate ((PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits).read j) x=0
    rw [PlayerSpecificAlgebraicTerminalLeafZeros.zero_resource p s B x hc hs hend hL j hz H K bits]
    rfl
  rw [he,Measure.map_const,measure_univ,one_smul]

theorem marginal_error {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight B T) (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (H K : ℕ) (j : Fin N) (z : ℝ) :
    |closedCDF (law p s B H K x) j z-
      (zeroUniformLaw (lengths p x j) (eval s x j/lengths p x j)).real (Set.Iic z)| ≤ PlayerSpecificTerminalCoreCDF.error H K := by
  let model := RationalCostModel.schoolbook
  let g := prepare model p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let U := PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T
  let core := PlayerSpecificTerminalCoreBranchLaws.law p.parameters a H K x
  have ha := PlayerSpecificAlgebraicTerminalCorePreparation.valid model p s B x hc hs hB hL hb hmass hend T hsize
  have hf := PlayerSpecificAlgebraicTerminalCorePreparationSizes.fits model p s B x hc hs hB hL hb hmass hend T hroot hml hBH hsize hresource
  have hTU : T ≤ U := by
    have h0 : T ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans (large _))
  have hU : 2 ≤ U := by
    have h0 : 2 ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans (large _))
  have hrootU := mono hroot hTU
  have hcount := groups_count model p s B x hc hs hB hL hb hmass hend
  obtain ⟨G,hGlength,hGmember,hGtotal,hpivot,hlaw⟩ :=
    PlayerSpecificTerminalLeafLawGeometry.geometry p s B x hc hs hB hL hb hmass hend T hsize H K
  by_cases hz : eval s x j=0
  · have hmarg := zero_marginal p s B x hc hs hend (fun k => (hL k).1) j hz H K
    simp only [closedCDF,hmarg,hz,zero_div,zeroUniformLaw,sub_zero,ENNReal.ofReal_one,one_smul,
      ENNReal.ofReal_zero,zero_smul,add_zero,sub_self,abs_zero]
    unfold PlayerSpecificTerminalCoreCDF.error
    positivity
  · by_cases hfr : Fractional (lengths p x) (eval s x) j
    · have hj := (fractional_value model p s B x hs hend j).mpr hfr
      have hsome : a.fractional=some ((p.rows.read j).length,
          PlayerSpecificAlgebraicField.divide p.parameters.root.polynomial (s.data.read j) (p.rows.read j).length) := by
        change (g.fractional.map _)=_
        rw [hj]
        rfl
      have h := PlayerSpecificTerminalCoreCDF.fractional p.parameters a hc.normalized hc.irreducible hc.interval x hc.root
        ha U hf hml hrootU hU H K _ _ hsome z
      have hq := PlayerSpecificAlgebraicField.divide_value p.parameters.root.polynomial (s.data.read j) (p.rows.read j).length
        hc.normalized hc.irreducible (hc.lengths j) x hc.root.1
      rw [hq] at h
      rw [hlaw,hj]
      unfold closedCDF
      rw [PlayerSpecificLeafMapLaw.pivot_marginal G j (hpivot j hj) core]
      exact h
    · have hpos : 0 < eval s x j := lt_of_le_of_ne (hb j).1 (Ne.symm hz)
      have hsat : eval s x j=lengths p x j := le_antisymm (hb j).2 (le_of_not_gt (fun hlt => hfr ⟨hpos,hlt⟩))
      obtain ⟨group,hmember⟩ := PlayerSpecificTerminalLeafLawGeometry.saturated_member model p s B x hc j hsat
      let q : Fin 3 := ⟨group.val,lt_of_lt_of_le group.isLt hcount.2⟩
      have hq : q.val < a.count := group.isLt
      have hslot : slot group=q.castSucc := by
        apply Fin.ext
        change group.val%4=group.val
        exact Nat.mod_eq_of_lt (lt_of_lt_of_le group.isLt (hcount.2.trans (by omega)))
      have hlength : realEvaluate (a.lengths.read q) x=realEvaluate (g.groups.get group).total x :=
        congrArg (fun row => realEvaluate row x) (PlayerSpecificAlgebraicTerminalCoreValues.length_read p s B g q group.isLt)
      have huniform : RealCDFClose (marginal core (slot group)) (uniformMarginal (G.total group) (G.total_pos group))
          (PlayerSpecificTerminalCoreCDF.error H K) := by
        intro t
        change |closedCDF core (slot group) t-(Blotto.uniformLaw (G.total group)).real (Set.Iic t)| ≤ _
        rw [hslot,hGtotal group,←hlength]
        exact PlayerSpecificTerminalCoreCDF.uniforms p.parameters a hc.normalized hc.irreducible hc.interval x hc.root
          ha U hf hml hrootU hU H K q hq t
      have h := PlayerSpecificLeafMapLaw.group_CDF G g.fractional hpivot group j ((hGmember group j).mpr hmember)
        core _ huniform z
      rw [hGlength j] at h
      rw [hlaw,hsat,div_self (ne_of_gt (hL j).1)]
      simpa only [zeroUniformLaw,sub_self,ENNReal.ofReal_zero,zero_smul,ENNReal.ofReal_one,one_smul,zero_add] using h

end Blotto.PlayerSpecificTerminalLeafCDF
