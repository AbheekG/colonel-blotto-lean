import Blotto.GeneralPaperComparatorSecurity
import Blotto.GeneralPaperClosedAlphabet
import Blotto.GeneralPaperResponsePhysicalHeights
import Blotto.GeneralPaperSourceAlphabetLower

/-! The actual closed decoder gives one finite rational bid set, containing
both endpoints and supporting every physical closed-code law. -/
namespace Blotto.GeneralPaperCandidateBidSet
open MeasureTheory
open GeneralPaperCodeAlphabet GeneralPaperClosedAlphabet
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable def bids (a : Alphabet) : Finset ℚ := Finset.univ.image (value a)

theorem value_mem (a : Alphabet) (i : Closed a) : value a i ∈ bids a :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem zero_mem (a : Alphabet) : (0 : ℚ) ∈ bids a := by
  simpa only [zero_value] using value_mem a (zero a)

def one (a : Alphabet) : Closed a :=
  ⟨⟨4 * a.C,by rw [← a.dyadic]; have h := a.scalePositive; omega⟩,valid_grid a false a.C le_rfl⟩

theorem one_value (a : Alphabet) : value a (one a) = 1 := by
  have he := (decoded a (one a)).symm.trans (GeneralPaperCodeDecodeSound.decode_one a false)
  have hc := Option.some.inj he
  unfold value
  rw [hc]
  exact grid_one a

theorem one_mem (a : Alphabet) : (1 : ℚ) ∈ bids a := by
  simpa only [one_value] using value_mem a (one a)

theorem unit (a : Alphabet) (bid : ℚ) (hb : bid ∈ bids a) : 0 ≤ bid ∧ bid ≤ 1 := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
  exact ⟨value_nonnegative a i,value_le_one a i⟩

theorem height (a : Alphabet) (bid : ℚ) (hb : bid ∈ bids a) :
    RationalHeight bid (a.lambda + 1) := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
  exact (GeneralPaperResponsePhysicalHeights.decoded_threshold a false i.val.val (choice a i) (decoded a i)).mono
    (GeneralPaperSourceAlphabetLower.scale_width a)

theorem decoded_mem (a : Alphabet) (code : ℕ) (selected : Choice)
    (hd : (GeneralPaperCodeDecode.decode a false code).choice = some selected) : selected.threshold.value ∈ bids a := by
  have hValid := GeneralPaperCodeDecodeSound.decode_valid a false code selected hd
  have hCode : code < 2 ^ a.lambda := by
    rw [← a.dyadic]
    exact valid_in_alphabet a false code hValid
  let i : Closed a := ⟨⟨code,hCode⟩,hValid⟩
  have hc : choice a i = selected := Option.some.inj ((decoded a i).symm.trans hd)
  have h := value_mem a i
  simpa only [value,hc] using h

theorem law_coordinates {m : ℕ} (a : Alphabet) (B : ℚ)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false B) (qbar : ℕ) :
    ∀ᵐ row ∂(GeneralPaperCodeMixturePhysical.physicalLaw X qbar : Measure (Allocation m)),
      ∀ j,∃ bid ∈ bids a,row j = (bid : ℝ) := by
  apply probabilityMixture_ae X.law.weight
    (fun l => PureBoundaryEquilibria.pointLaw (GeneralPaperCodeMixturePhysical.allocation X qbar l)) X.law.nonnegative X.law.total
  intro l
  change ∀ᵐ row ∂Measure.dirac (GeneralPaperCodeMixturePhysical.allocation X qbar l),_
  rw [ae_dirac_eq]
  intro j
  refine ⟨((X.choices l).read j).threshold.value,decoded_mem a _ _ (X.decoded l j),?_⟩
  have hClosed := GeneralPaperCodeDecodeSound.candidate_closed a _ _ (X.decoded l j)
  simp only [GeneralPaperCodeMixturePhysical.allocation,Choice.physical,hClosed,Bool.false_eq_true,ite_false,add_zero]

end Blotto.GeneralPaperCandidateBidSet
