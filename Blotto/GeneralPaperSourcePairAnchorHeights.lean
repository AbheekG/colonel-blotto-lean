import Blotto.GeneralPaperClosedArithmeticSampling

/-! Both actual returned source dictionaries have bounded rational anchors,
whether the classifier modifies rich, poor, or neither. Original native
columns inherit this bound through their proved physical Matches return.
All heights are erased analysis; no extra source or encoding pass runs. -/
namespace Blotto.GeneralPaperSourcePairAnchorHeights
open GeneralPaperProxyParameters GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def width (m k : ℕ) : ℕ :=
  max (GeneralPaperSourceScoreHeights.anchorHeight m k) (GeneralPaperEndpointDictionarySize.width m k)

theorem unchanged {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (j : Fin m) (l : Fin (prepare m k).K) :
    RationalHeight ((GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal).anchor j l) (width m k) :=
  (GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l).mono (le_max_left _ _)

theorem pair_height {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (pair : GeneralPaperSourcePairRun.Pair (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (hRun : GeneralPaperSourcePairRun.run k Qv hQv weights hp hs b=some pair) :
    (∀ j l,RationalHeight (pair.rich.anchor j l) (width m k)) ∧
      (∀ j l,RationalHeight (pair.poor.anchor j l) (width m k)) := by
  obtain ⟨checked,hChecked,_hContract,hRich,hPoor⟩ :=
    GeneralPaperCheckedPairEndpointSize.run_contract k Qv hm hQv weights hp hs b hb
  rw [GeneralPaperCheckedSourcePair.run_eq k Qv hm hQv weights hp hs b hb] at hChecked
  have he : checked=pair := Option.some.inj (hChecked.symm.trans hRun)
  subst checked
  cases hc : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none =>
    have he := hRun
    simp only [GeneralPaperSourcePairRun.run,hc,Option.some.injEq] at he
    rw [←he]
    exact ⟨unchanged k Qv hQv weights hp hs b hb false,unchanged k Qv hQv weights hp hs b hb true⟩
  | some side =>
    cases side with
    | rich =>
      have hMap := hRun
      rw [GeneralPaperSourcePairRun.run,hc] at hMap
      obtain ⟨d,_hd,he⟩ := Option.map_eq_some_iff.mp hMap
      refine ⟨fun j l => (hRich hc j l).mono (le_max_right _ _),?_⟩
      rw [←he]
      exact unchanged k Qv hQv weights hp hs b hb true
    | poor =>
      have hMap := hRun
      rw [GeneralPaperSourcePairRun.run,hc] at hMap
      obtain ⟨d,_hd,he⟩ := Option.map_eq_some_iff.mp hMap
      refine ⟨?_,fun j l => (hPoor hc j l).mono (le_max_right _ _)⟩
      rw [←he]
      exact unchanged k Qv hQv weights hp hs b hb false

theorem physical_height {T m K H : ℕ} (physical : Columns T m K) (pair : GeneralPaperSourcePairRun.Pair T m K)
    (hMatches : Matches physical pair)
    (hRich : ∀ j l,RationalHeight (pair.rich.anchor j l) H) (hPoor : ∀ j l,RationalHeight (pair.poor.anchor j l) H) :
    (∀ j l,RationalHeight (((physical.rich.read j).anchors).read l) H) ∧
      (∀ j l,RationalHeight (((physical.poor.read j).anchors).read l) H) := by
  constructor
  · intro j l
    change RationalHeight ((GeneralPaperRowQuantizer.dictionary physical.rich).anchor j l) H
    rw [hMatches.1]
    exact hRich j l
  · intro j l
    change RationalHeight ((GeneralPaperRowQuantizer.dictionary physical.poor).anchor j l) H
    rw [hMatches.2]
    exact hPoor j l

theorem original_bit_return {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
    ∃ physical,(GeneralPaperOriginalSourceValueDriver.bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      (∀ j l,RationalHeight (((physical.rich.read j).anchors).read l) (width o.reduced.m k)) ∧
      (∀ j l,RationalHeight (((physical.poor.read j).anchors).read l) (width o.reduced.m k)) := by
  obtain ⟨physical,pair,hNative,hSource,hMatches,_hContract⟩ :=
    GeneralPaperOriginalSourceValueDriver.bit_return model Wv Ws k values v hv b hb
  let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
  have hRun : GeneralPaperSourcePairRun.run k o.Qv o.Qv_positive o.weights o.weights_positive o.weight_sum (b:ℝ)=some pair := hSource
  have h := pair_height k o.Qv (GeneralPaperOriginalSourceValuePreparation.count_bounds true model Wv k values v hv).1
    o.Qv_positive o.weights o.weights_positive o.weight_sum (b:ℝ) (by exact_mod_cast hb) pair hRun
  exact ⟨physical,hNative,physical_height physical pair hMatches h.1 h.2⟩


@[fun_prop]
theorem width_rate : GeneralPaperSourceRateAlgebra.Rated
    (fun x : GeneralPaperSourceWordGrowth.Input => width x.m x.k) 1 0 1 := by
  have hA := GeneralPaperSourceSharpOperandRates.anchor_height
  have hQ := GeneralPaperSourceSharpOperandRates.cap_word
  have hH := GeneralPaperBasisStorageRates.determinant_length
  exact GeneralPaperSourceRateAlgebra.maximum _ _ 1 0 1 1 0 1 hA
    (GeneralPaperSourceRateAlgebra.add _ _ 1 0 1 1 0 1 hQ hH)

theorem width_soft : ∃ C d : ℕ,∀ x : GeneralPaperSourceWordGrowth.Input,
    width x.m x.k≤C*(x.m+1)*2^x.k*(GeneralPaperSourceWordGrowth.logSize x)^d := by
  obtain ⟨C,d,h⟩ := width_rate
  refine ⟨C,d,?_⟩
  intro x
  simpa only [GeneralPaperSourceRateAlgebra.monomial,GeneralPaperNativeSourceRates.fields,
    GeneralPaperNativeSourceRates.accuracy,pow_one,pow_zero,Nat.mul_one,Nat.mul_assoc] using h x

end Blotto.GeneralPaperSourcePairAnchorHeights
