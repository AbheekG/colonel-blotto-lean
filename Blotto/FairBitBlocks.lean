import Blotto.FairBitFiniteAverage

/-! Two fresh fair bit blocks can be supplied by one flat fair vector. The
law identity verifies their independence and fixes the total bit allocation;
the finite sums below are proof representations only. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

def firstBitBlock (R K : ℕ) (bits : Fin (R + K) → Bool) : Fin R → Bool :=
  fun i => bits (Fin.castAdd K i)

def secondBitBlock (R K : ℕ) (bits : Fin (R + K) → Bool) : Fin K → Bool :=
  fun i => bits (Fin.natAdd R i)

def bitBlockEquiv (R K : ℕ) : ((Fin K → Bool) × (Fin R → Bool)) ≃ (Fin (R + K) → Bool) where
  toFun := fun p => Fin.append p.2 p.1
  invFun := fun bits => (secondBitBlock R K bits, firstBitBlock R K bits)
  left_inv := by
    rintro ⟨scalar, choice⟩
    apply Prod.ext <;> funext i <;> simp [firstBitBlock, secondBitBlock]
  right_inv := fun bits => Fin.append_castAdd_natAdd

theorem fairBitLaw_map_atoms {α : Type*} [MeasurableSpace α] (R : ℕ) (f : (Fin R → Bool) → α) :
    ((fairBitLaw R).map f : Measure α) =
      Measure.sum (fun bits => ENNReal.ofReal (1 / (2 : ℝ) ^ R) • Measure.dirac (f bits)) := by
  have hf : Measurable f := measurable_of_countable _
  change Measure.map f (fairBitLaw R : Measure (Fin R → Bool)) = _
  rw [fairBitLaw_atoms, Measure.map_sum hf.aemeasurable]
  simp_rw [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]

theorem fairBitBlocks_law {n : ℕ} (R K : ℕ) (f : (Fin R → Bool) → (Fin K → Bool) → Allocation n) :
    (fairBitLaw (R + K)).map (fun bits => f (firstBitBlock R K bits) (secondBitBlock R K bits)) =
      averagedLaw (fairBitLaw K) (fun scalar => (fairBitLaw R).map (fun choice => f choice scalar))
        (measurable_of_countable _) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [fairBitLaw_map_atoms]
  have hfamily : Measurable (fun scalar : Fin K → Bool =>
      ((fairBitLaw R).map (fun choice => f choice scalar) : Measure (Allocation n))) := measurable_of_countable _
  change Measure.sum (fun bits => ENNReal.ofReal (1 / (2 : ℝ) ^ (R + K)) •
    Measure.dirac (f (firstBitBlock R K bits) (secondBitBlock R K bits))) =
    (fairBitLaw K : Measure (Fin K → Bool)).bind
      (fun scalar => ((fairBitLaw R).map (fun choice => f choice scalar) : Measure (Allocation n)))
  rw [fairBitLaw_atoms, Measure.bind_sum _ _ hfamily.aemeasurable]
  simp_rw [Measure.bind_smul _ _ hfamily.aemeasurable, Measure.dirac_bind hfamily, fairBitLaw_map_atoms]
  simp_rw [Measure.sum_fintype, Finset.smul_sum, smul_smul]
  have hsum : (∑ blocks : (Fin K → Bool) × (Fin R → Bool),
      (ENNReal.ofReal (1 / (2 : ℝ) ^ K) * ENNReal.ofReal (1 / (2 : ℝ) ^ R)) • Measure.dirac (f blocks.2 blocks.1)) =
      ∑ scalar : Fin K → Bool, ∑ choice : Fin R → Bool,
        (ENNReal.ofReal (1 / (2 : ℝ) ^ K) * ENNReal.ofReal (1 / (2 : ℝ) ^ R)) • Measure.dirac (f choice scalar) :=
    Fintype.sum_prod_type _
  rw [← hsum]
  rw [← Equiv.sum_comp (bitBlockEquiv R K)]
  apply Finset.sum_congr rfl
  intro blocks _
  have hw : ENNReal.ofReal (1 / (2 : ℝ) ^ (R + K)) =
      ENNReal.ofReal (1 / (2 : ℝ) ^ K) * ENNReal.ofReal (1 / (2 : ℝ) ^ R) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 : ℝ) ^ K)]
    congr 1
    rw [pow_add]
    field_simp
  rw [hw]
  congr 1
  change Measure.dirac (f (firstBitBlock R K (Fin.append blocks.2 blocks.1))
    (secondBitBlock R K (Fin.append blocks.2 blocks.1))) = Measure.dirac (f blocks.2 blocks.1)
  have hfirst : firstBitBlock R K (Fin.append blocks.2 blocks.1) = blocks.2 := by
    funext i
    exact Fin.append_left _ _ i
  have hsecond : secondBitBlock R K (Fin.append blocks.2 blocks.1) = blocks.1 := by
    funext i
    exact Fin.append_right _ _ i
  rw [hfirst, hsecond]

end Blotto
