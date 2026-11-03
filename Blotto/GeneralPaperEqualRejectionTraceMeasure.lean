import Blotto.GeneralPaperEqualRejectionPrefix

/-! The uncapped fair-bit computation as a countable measure of its finite
first-success traces. A trace contains the rejected blocks, one accepted
block, then the midpoint bits. Each level is the actual fair-vector measure
restricted to this operational first-success event; its total mass is derived
and the countable levels sum to one. No stopping distribution is supplied. -/
namespace Blotto.GeneralPaperEqualRejectionTraceMeasure
open MeasureTheory Set
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 700000
open UniformNatRejection (width attempt acceptance)
open GeneralPaperEqualRejectionAllocation (mean_commute mean_mul)

abbrev length (N K cap : ℕ) : ℕ := cap * width N + (width N + K)
abbrev Trace (N K : ℕ) := Σ cap : ℕ, (Fin (length N K cap) → Bool)

@[instance_reducible] def traceMeasurableSpace (N K : ℕ) : MeasurableSpace (Trace N K) := ⊤
attribute [instance] traceMeasurableSpace

theorem trace_singletons (N K : ℕ) : MeasurableSingletonClass (Trace N K) := by
  constructor
  intro trace
  trivial
attribute [instance] trace_singletons

def priorBits (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) : Fin (cap * width N) → Bool :=
  firstBitBlock (cap * width N) (width N + K) bits

def last (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) : Fin (width N) → Bool :=
  firstBitBlock (width N) K (secondBitBlock (cap * width N) (width N + K) bits)

def scalar (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) : Fin K → Bool :=
  secondBitBlock (width N) K (secondBitBlock (cap * width N) (width N + K) bits)

def Good (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) : Prop :=
  (GeneralPaperEqualRejectionReads.run N cap (priorBits N K cap bits)).output = none ∧
    (attempt N (last N K cap bits)).isSome

def test (N K cap : ℕ) (f : Fin N → (Fin K → Bool) → ℝ)
    (bits : Fin (length N K cap) → Bool) : ℝ :=
  if (GeneralPaperEqualRejectionReads.run N cap (priorBits N K cap bits)).output = none then
    match attempt N (last N K cap bits) with
    | none => 0
    | some r => f r (scalar N K cap bits)
  else 0

theorem single_mean (N K : ℕ) (hN : 0 < N) (f : Fin N → (Fin K → Bool) → ℝ) :
    (fairBitKernel (width N + K)).mean (fun bits =>
      match attempt N (firstBitBlock (width N) K bits) with
      | none => 0 | some r => f r (secondBitBlock (width N) K bits)) =
      (acceptance N : ℝ) * (UniformNatRejection.targetKernel N hN).mean
        (fun r => (fairBitKernel K).mean (f r)) := by
  rw [fairBitKernel_blocks (width N) K
    (fun first scalar => match attempt N first with | none => 0 | some r => f r scalar)]
  rw [mean_commute (width N) K]
  have he : ∀ scalar : Fin K → Bool,
      (fairBitKernel (width N)).mean (fun first =>
        match attempt N first with | none => 0 | some r => f r scalar) =
        (acceptance N : ℝ) * (UniformNatRejection.targetKernel N hN).mean (fun r => f r scalar) := by
    intro scalar
    have h := UniformNatRejection.attemptKernel_mean N hN
      (fun result => match result with | none => 0 | some r => f r scalar)
    simpa only [UniformNatRejection.attemptKernel, BoundedExpectationKernel.map,
      BoundedExpectationKernel.bind, BoundedExpectationKernel.point, mul_zero, add_zero] using h
  simp_rw [he]
  rw [mean_mul]
  change _ = (acceptance N : ℝ) * ((1 / (N : ℝ)) * ∑ r, (fairBitKernel K).mean (f r))
  congr 1
  change (fairBitKernel K).mean (fun b => (1 / (N : ℝ)) * ∑ r, f r b) = _
  rw [mean_mul]
  have hs := GeneralPaperEqualRejectionAllocation.mean_weighted K (fun _ : Fin N => (1 : ℝ)) f
  simp only [one_mul] at hs
  rw [hs]

theorem level_mean (N K cap : ℕ) (hN : 0 < N) (f : Fin N → (Fin K → Bool) → ℝ) :
    (fairBitKernel (length N K cap)).mean (test N K cap f) =
      rejectionFailure (acceptance N : ℝ) cap * (acceptance N : ℝ) *
        (UniformNatRejection.targetKernel N hN).mean (fun r => (fairBitKernel K).mean (f r)) := by
  unfold test priorBits last scalar length
  rw [fairBitKernel_blocks (cap * width N) (width N + K)
    (fun first rest => if (GeneralPaperEqualRejectionReads.run N cap first).output = none then
      match attempt N (firstBitBlock (width N) K rest) with
      | none => 0 | some r => f r (secondBitBlock (width N) K rest)
      else 0)]
  have he : ∀ first : Fin (cap * width N) → Bool,
      (fairBitKernel (width N + K)).mean (fun rest =>
        if (GeneralPaperEqualRejectionReads.run N cap first).output = none then
          match attempt N (firstBitBlock (width N) K rest) with
          | none => 0 | some r => f r (secondBitBlock (width N) K rest)
        else 0) =
      ((acceptance N : ℝ) * (UniformNatRejection.targetKernel N hN).mean
        (fun r => (fairBitKernel K).mean (f r))) *
        (if (GeneralPaperEqualRejectionReads.run N cap first).output = none then 1 else 0) := by
    intro first
    by_cases h : (GeneralPaperEqualRejectionReads.run N cap first).output = none
    · simp only [h, ite_true, mul_one]
      exact single_mean N K hN f
    · simp only [h, ite_false, mul_zero, (fairBitKernel _).constant]
  simp_rw [he]
  rw [mean_mul]
  simp_rw [GeneralPaperEqualRejectionReads.output]
  rw [UniformNatRejection.run_failure_mass N hN cap]
  ring

theorem test_one (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) :
    test N K cap (fun _ _ => 1) bits = if Good N K cap bits then 1 else 0 := by
  unfold test Good
  by_cases hp : (GeneralPaperEqualRejectionReads.run N cap (priorBits N K cap bits)).output = none
  · simp only [hp, ite_true, true_and]
    cases attempt N (last N K cap bits) <;> rfl
  · simp only [hp, ite_false, false_and]

noncomputable def part (N K cap : ℕ) : Measure (Fin (length N K cap) → Bool) :=
  (fairBitLaw (length N K cap) : Measure (Fin (length N K cap) → Bool)).restrict {bits | Good N K cap bits}

theorem part_mass (N K cap : ℕ) (hN : 0 < N) :
    part N K cap Set.univ = ENNReal.ofReal (rejectionFailure (acceptance N : ℝ) cap * (acceptance N : ℝ)) := by
  have h := level_mean N K cap hN (fun _ _ => 1)
  simp only [(fairBitKernel K).constant, (UniformNatRejection.targetKernel N hN).constant, mul_one] at h
  have ht : test N K cap (fun _ _ => 1) = fun bits => if Good N K cap bits then 1 else 0 :=
    funext (test_one N K cap)
  rw [ht] at h
  change (fairBitKernel (length N K cap)).mean
    (fun bits => if bits ∈ {bits | Good N K cap bits} then (1 : ℝ) else 0) = _ at h
  rw [← GeneralPaperEqualRejectionAllocation.fair_event] at h
  unfold part
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [← h]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

noncomputable def measure (N K : ℕ) : Measure (Trace N K) :=
  Measure.sum (fun cap => Measure.map (Sigma.mk cap) (part N K cap))

theorem success_mass_hasSum (N : ℕ) (hN : 0 < N) :
    HasSum (fun cap => rejectionFailure (acceptance N : ℝ) cap * (acceptance N : ℝ)) 1 := by
  have ha := UniformNatRejection.acceptance_bounds N hN
  have hp : (0 : ℝ) < acceptance N := by linarith only [ha.1]
  have hs := (hasSum_geometric_of_lt_one (by linarith only [ha.2] : (0 : ℝ) ≤ 1 - acceptance N)
    (by linarith only [ha.1] : (1 : ℝ) - acceptance N < 1)).mul_right (acceptance N : ℝ)
  simpa only [rejectionFailure, sub_sub_cancel, inv_mul_cancel₀ hp.ne'] using hs

theorem mass (N K : ℕ) (hN : 0 < N) : measure N K Set.univ = 1 := by
  unfold measure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ, part_mass N K _ hN]
  have ha := UniformNatRejection.acceptance_bounds N hN
  have hs := success_mass_hasSum N hN
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun cap => mul_nonneg (rejectionFailure_unit (by linarith only [ha.1]) ha.2 cap).1
      (by linarith only [ha.1])) hs.summable, hs.tsum_eq]
  norm_num

noncomputable def law (N K : ℕ) (hN : 0 < N) : ProbabilityMeasure (Trace N K) :=
  ⟨measure N K, ⟨mass N K hN⟩⟩

theorem good_ae (N K : ℕ) (hN : 0 < N) :
    ∀ᵐ trace ∂(law N K hN : Measure (Trace N K)), Good N K trace.1 trace.2 := by
  change ∀ᵐ trace ∂measure N K, Good N K trace.1 trace.2
  apply Measure.ae_sum_iff.mpr
  intro cap
  rw [ae_map_iff (measurable_of_countable _).aemeasurable
    ((Set.to_countable {trace : Trace N K | Good N K trace.1 trace.2}).measurableSet)]
  exact ae_restrict_mem (Set.toFinite _).measurableSet

theorem singleton_mass (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) :
    measure N K {⟨cap, bits⟩} =
      if Good N K cap bits then ENNReal.ofReal (1 / (2 : ℝ) ^ length N K cap) else 0 := by
  unfold measure
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  rw [tsum_eq_single cap]
  · rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have he : (Sigma.mk cap) ⁻¹' ({⟨cap, bits⟩} : Set (Trace N K)) = {bits} := by ext x; simp
    rw [he, part, Measure.restrict_apply (measurableSet_singleton _)]
    by_cases hg : Good N K cap bits
    · simp only [hg, ite_true]
      have hs : {bits} ∩ {x | Good N K cap x} = {bits} := by ext x; simp [hg]
      rw [hs, fairBitLaw_singleton_realWeight]
    · simp only [hg, ite_false]
      have hs : {bits} ∩ {x | Good N K cap x} = ∅ := by ext x; simp [hg]
      rw [hs, measure_empty]
  · intro other hn
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have he : (Sigma.mk other) ⁻¹' ({⟨cap, bits⟩} : Set (Trace N K)) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hn (congrArg Sigma.fst h)
    rw [he, measure_empty]

def codeWord (N K cap : ℕ) (tape : ℕ → Fin (width N) → Bool) (midpoint : Fin K → Bool) :
    Fin (length N K cap) → Bool :=
  Fin.append (GeneralPaperEqualRejectionPrefix.seed (width N) cap tape) (Fin.append (tape cap) midpoint)

theorem word_parts (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) :
    Fin.append (priorBits N K cap bits) (Fin.append (last N K cap bits) (scalar N K cap bits)) = bits := by
  calc
    _ = Fin.append (priorBits N K cap bits)
        (secondBitBlock (cap * width N) (width N + K) bits) := by
      congr 1
      exact Fin.append_castAdd_natAdd
    _ = bits := Fin.append_castAdd_natAdd

theorem good_realization (N K cap : ℕ) (bits : Fin (length N K cap) → Bool) (h : Good N K cap bits) :
    ∃ (tape : ℕ → Fin (width N) → Bool) (r : Fin N),
      codeWord N K cap tape (scalar N K cap bits) = bits ∧
        GeneralPaperEqualRejectionPrefix.blockRun N (cap + 1) tape =
          ⟨some r, (cap + 1) * width N⟩ := by
  obtain ⟨prior, hp⟩ := GeneralPaperEqualRejectionPrefix.seed_surjective (width N) cap (priorBits N K cap bits)
  let tape := Function.update prior cap (last N K cap bits)
  have hs : GeneralPaperEqualRejectionPrefix.seed (width N) cap tape = priorBits N K cap bits := by
    rw [← hp]
    apply GeneralPaperEqualRejectionPrefix.seed_congr
    intro t ht
    exact Function.update_of_ne (by omega) _ _
  have hl : tape cap = last N K cap bits := Function.update_self _ _ _
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h.2
  have hf : (GeneralPaperEqualRejectionPrefix.blockRun N cap tape).output = none := by
    rw [← GeneralPaperEqualRejectionPrefix.run_seed, hs]
    exact h.1
  have ha : attempt N (tape cap) = some r := by rw [hl]; exact hr
  refine ⟨tape, r, ?_, GeneralPaperEqualRejectionPrefix.first_success N cap tape r
    ((GeneralPaperEqualRejectionPrefix.failure_all N cap tape).mp hf) ha⟩
  unfold codeWord
  rw [hs, hl]
  exact word_parts N K cap bits

theorem operational_termination_ae (N K : ℕ) (hN : 0 < N) :
    ∀ᵐ trace ∂(law N K hN : Measure (Trace N K)),
      ∃ (tape : ℕ → Fin (width N) → Bool) (r : Fin N),
        codeWord N K trace.1 tape (scalar N K trace.1 trace.2) = trace.2 ∧
          GeneralPaperEqualRejectionPrefix.blockRun N (trace.1 + 1) tape =
            ⟨some r, (trace.1 + 1) * width N⟩ :=
  (good_ae N K hN).mono fun trace h => good_realization N K trace.1 trace.2 h

theorem completes_ae (N K : ℕ) (hN : 0 < N) :
    ∀ᵐ trace ∂(law N K hN : Measure (Trace N K)),
      ∃ (tape : ℕ → Fin (width N) → Bool) (r : Fin N),
        codeWord N K trace.1 tape (scalar N K trace.1 trace.2) = trace.2 ∧
          GeneralPaperEqualRejectionPrefix.Completes N tape r ((trace.1 + 1) * width N) := by
  apply (operational_termination_ae N K hN).mono
  intro trace h
  obtain ⟨tape, r, hc, hr⟩ := h
  exact ⟨tape, r, hc, trace.1 + 1, hr⟩

end Blotto.GeneralPaperEqualRejectionTraceMeasure
