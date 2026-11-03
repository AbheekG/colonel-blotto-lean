import Blotto.GeneralPaperOrderedSelectedProfitGuarantee

/-! Actual native nonnegative option profits for the two source optimizers.
One cached signed-tail plan supplies both signs with a common mesh normalizer.
The coefficient 2*T*v_j is formed once per field/round. Resource tags are
copied exactly from the prepared option catalogue, whose physical semantics
and costs remain a required source join.
-/
namespace Blotto.GeneralPaperOrderedNativeOptionProfits
open scoped BigOperators
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

structure Plan (R : Type) (k K : ℕ) where
  tags : FixedArrayTable K R
  mesh : ℕ
  tails : GeneralPaperSignedTailPlan.Plan k K

def prepare {K : ℕ} (k U : ℕ) (summary : Summary k) (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) : Plan R k K :=
  ⟨tags,(GeneralPaperSourceParameters.prepare k).meshDenominator,GeneralPaperSignedTailPlan.prepare k U summary codes⟩

def build {K : ℕ} (k T weight : ℕ) (preparedPrefix : Prefix k) (plan : Plan R k K) : GeneralPaperOrderedProfitDP.Field R K × ℕ :=
  let coefficient := 2*T*weight
  let filled := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
    let queried := GeneralPaperSignedTailPlan.evaluate k preparedPrefix plan.tails i
    ((coefficient*(plan.mesh+queried.positive-queried.negative),plan.tags.read i),queried.work+24))
  (filled.1,filled.2+16)

theorem read_build {K : ℕ} (k T weight : ℕ) (preparedPrefix : Prefix k) (plan : Plan R k K) (i : Fin K) :
    (build k T weight preparedPrefix plan).1.read i=
      (2*T*weight*(plan.mesh+(GeneralPaperSignedTailPlan.evaluate k preparedPrefix plan.tails i).positive-
        (GeneralPaperSignedTailPlan.evaluate k preparedPrefix plan.tails i).negative),plan.tags.read i) := by
  rw [build,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem tag_preserved {K : ℕ} (k T weight : ℕ) (preparedPrefix : Prefix k) (plan : Plan R k K) (i : Fin K) :
    ((build k T weight preparedPrefix plan).1.read i).2=plan.tags.read i := by rw [read_build]

theorem numerator_bound {K : ℕ} (k U T weight : ℕ) (summary values : Summary k) (hTotal : 0<∑ r, values.read r)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) (i : Fin K) :
    ((build k T weight (GeneralPaperEpochPrefixArray.build values) (prepare k U summary codes tags)).1.read i).1≤
      2*(2*T*(GeneralPaperSourceParameters.prepare k).meshDenominator)*weight := by
  rw [read_build]
  have hp := GeneralPaperSignedTailValues.evaluate_bounds k U summary values hTotal codes i
  have hc : (GeneralPaperSourceParameters.prepare k).meshDenominator+
      (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build values) (GeneralPaperSignedTailPlan.prepare k U summary codes) i).positive-
      (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build values) (GeneralPaperSignedTailPlan.prepare k U summary codes) i).negative≤
      2*(GeneralPaperSourceParameters.prepare k).meshDenominator := by omega
  have he := Nat.mul_le_mul_left (2*T*weight) hc
  simpa only [prepare,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using he

theorem numerator_ratio (T weight Qv N pos neg : ℕ) (hT : 0<T) (hQv : 0<Qv) (hN : 0<N) (hNeg : neg≤N) :
    ((2*T*weight*(N+pos-neg):ℕ):ℚ)/((2*T*Qv*N:ℕ):ℚ)=
      (weight:ℚ)/Qv*(1+((pos:ℚ)/N-(neg:ℚ)/N)) := by
  have ht : (T:ℚ)≠0 := by exact_mod_cast hT.ne'
  have hq : (Qv:ℚ)≠0 := by exact_mod_cast hQv.ne'
  have hn : (N:ℚ)≠0 := by exact_mod_cast hN.ne'
  have hs : neg≤N+pos := by omega
  simp only [Nat.cast_mul,Nat.cast_sub hs,Nat.cast_add,Nat.cast_ofNat]
  field_simp [ht,hq,hn]
  <;> ring

theorem normalized_value {K : ℕ} (m lambda k Qv U weight : ℕ) (hQv : 0<Qv)
    (summary values : Summary k) (hTotal : 0<∑ r, values.read r) (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) (i : Fin K) :
    ((((build k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weight (GeneralPaperEpochPrefixArray.build values)
      (prepare k U summary codes tags)).1.read i).1:ℕ):ℚ)/(GeneralPaperProfitParameters.parameters m lambda k Qv).qProf=
      (weight:ℚ)/Qv*(1+GeneralPaperSignedTailValues.value k
        (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build values) (GeneralPaperSignedTailPlan.prepare k U summary codes) i)) := by
  rw [read_build,GeneralPaperProfitParameters.qProf_spec]
  change ((2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*weight*
    ((GeneralPaperSourceParameters.prepare k).meshDenominator+_-_):ℕ):ℚ)/_= _
  unfold GeneralPaperSignedTailValues.value GeneralPaperRoundedLosses.component
  exact numerator_ratio _ weight Qv _ _ _ (GeneralPaperTrajectoryParameters.rows_positive lambda k) hQv
    (GeneralPaperSourceParameters.mesh_positive k) (GeneralPaperSignedTailValues.evaluate_bounds k U summary values hTotal codes i).2

theorem build_work {K : ℕ} (k T weight : ℕ) (preparedPrefix : Prefix k) (plan : Plan R k K) :
    (build k T weight preparedPrefix plan).2=K*(24*(30+k)+190)+34 := by
  rw [build,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [GeneralPaperSignedTailPlan.evaluate_work,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

end Blotto.GeneralPaperOrderedNativeOptionProfits
