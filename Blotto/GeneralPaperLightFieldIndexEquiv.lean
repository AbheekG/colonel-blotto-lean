import Blotto.GeneralPaperDictionaryUniformLaw

/-! The native returned heavy/light index arrays give an actual bijection
from concatenated fields to the original named fields. This is erased
analysis of retained arrays, with no supplied permutation or rescan. -/
namespace Blotto.GeneralPaperLightFieldIndexEquiv
open GeneralPaperLightFieldScan GeneralPaperLightFieldOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def mapping {n : ℕ} (state : State n) : Fin (state.heavy.size+state.light.size) → Fin n :=
  Fin.addCases (index state.heavy) (index state.light)

theorem heavy_read {n : ℕ} (state : State n) (j : Fin state.heavy.size) :
    mapping state (Fin.castAdd state.light.size j)=index state.heavy j := by
  simp only [mapping,Fin.addCases_left]

theorem light_read {n : ℕ} (state : State n) (j : Fin state.light.size) :
    mapping state (Fin.natAdd state.heavy.size j)=index state.light j := by
  simp only [mapping,Fin.addCases_right]

theorem injective {n : ℕ} (state : State n)
    (hH : StrictMono (index state.heavy)) (hL : StrictMono (index state.light))
    (hD : ∀ (i:Fin state.heavy.size) (j:Fin state.light.size),index state.heavy i≠index state.light j) :
    Function.Injective (mapping state) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro a j
    refine Fin.addCases ?_ ?_ j
    · intro b he
      simp only [heavy_read] at he
      exact congrArg (Fin.castAdd state.light.size) (hH.injective he)
    · intro b he
      simp only [heavy_read,light_read] at he
      exact False.elim (hD a b he)
  · intro a j
    refine Fin.addCases ?_ ?_ j
    · intro b he
      simp only [heavy_read,light_read] at he
      exact False.elim (hD b a he.symm)
    · intro b he
      simp only [light_read] at he
      exact congrArg (Fin.natAdd state.heavy.size) (hL.injective he)

theorem scan_bijective {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ) :
    Function.Bijective (mapping (scan bits model W r Q weights n le_rfl).1) := by
  let state := (scan bits model W r Q weights n le_rfl).1
  have hH : StrictMono (index state.heavy) := index_strictMono _ (heavy_ordered bits model W r Q weights n le_rfl)
  have hL : StrictMono (index state.light) := index_strictMono _ (light_ordered bits model W r Q weights n le_rfl)
  have hD : ∀ (i:Fin state.heavy.size) (j:Fin state.light.size),index state.heavy i≠index state.light j := by
    intro i j he
    have hi := (heavy_mem bits model W r Q weights n le_rfl (index state.heavy i)).mp
      (Array.mem_of_getElem (h:=i.isLt) rfl)
    have hj := (light_mem bits model W r Q weights n le_rfl (index state.light j)).mp
      (Array.mem_of_getElem (h:=j.isLt) rfl)
    rw [he] at hi
    exact (not_lt_of_ge hj.2) hi.2
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨injective state hH hL hD,by simpa only [Fintype.card_fin] using sizes bits model W r Q weights n le_rfl⟩

theorem classified_bijective {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    Function.Bijective (mapping (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1) := by
  rw [GeneralPaperLightFieldClassification.data]
  exact scan_bijective bits model W _ Q weights

theorem reduced_bijective {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    Function.Bijective (mapping (GeneralPaperReducedValuesDriver.run bits model W k Q weights).1.classified) := by
  rw [(GeneralPaperReducedValuesDriver.retained bits model W k Q weights).2.2.1]
  exact classified_bijective bits model W k Q weights

theorem original_bijective {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    Function.Bijective (mapping (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified) := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact reduced_bijective bits model W k _ _

noncomputable def originalEquiv {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    Fin ((GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.heavy.size+
      (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size) ≃ Fin n :=
  Equiv.ofBijective _ (original_bijective bits model W k values)

theorem original_equiv_apply {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (j : Fin ((GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.heavy.size+
      (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size)) :
    originalEquiv bits model W k values j=mapping (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified j := rfl

end Blotto.GeneralPaperLightFieldIndexEquiv
