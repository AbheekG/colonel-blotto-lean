import Blotto.PlayerSpecificAlgebraicDescriptorBinarySizes

/-! Any endpoint property transfers through the exact assembly references;
this covers budgets and boxes without ignoring zero-weight slots. -/
namespace Blotto.PlayerSpecificSegmentAssemblyProperties
open PlayerSpecificSegmentAssemblyReference
open PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicSegment PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

theorem pad_property {N k : ℕ} (l : SegmentLottery N k) (m : ℕ) (fallback : Fin k) (P : Allocation N → Prop)
    (h : ∀ slot,P (l.P slot) ∧ P (l.Q slot)) :
    ∀ slot,P ((pad l m fallback).P slot) ∧ P ((pad l m fallback).Q slot) := by
  intro slot
  refine Fin.addCases ?_ ?_ slot
  · intro j; simpa only [pad,Fin.addCases_left] using h j
  · intro j; simpa only [pad,Fin.addCases_right] using h fallback

theorem binary_property {N k m : ℕ} (p : ℝ) (hp : 0≤p ∧ p≤1) (l : SegmentLottery N k) (r : SegmentLottery N m)
    (P : Allocation N → Prop) (hl : ∀ slot,P (l.P slot) ∧ P (l.Q slot)) (hr : ∀ slot,P (r.P slot) ∧ P (r.Q slot)) :
    ∀ slot,P ((binary p hp l r).P slot) ∧ P ((binary p hp l r).Q slot) := by
  intro slot
  refine Fin.addCases ?_ ?_ slot
  · intro j; simpa only [binary,Fin.addCases_left] using hl j
  · intro j; simpa only [binary,Fin.addCases_right] using hr j

theorem bounds_mono {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (T U : ℕ)
    (h : Bounds root d T) (hTU : T≤U) : Bounds root d U := by
  constructor
  · intro slot; exact ⟨(h.weights slot).1,mono (h.weights slot).2 hTU⟩
  · intro slot j; exact ⟨(h.first slot j).1,mono (h.first slot j).2 hTU⟩
  · intro slot j; exact ⟨(h.second slot j).1,mono (h.second slot j).2 hTU⟩

end Blotto.PlayerSpecificSegmentAssemblyProperties
