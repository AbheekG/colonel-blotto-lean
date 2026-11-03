import Blotto.PlayerSpecificAlgebraicNestedInput

/-! A reached nested component shifts only its third coordinate. All
weights are reused; each changed endpoint is one reduced addition. -/
namespace Blotto.PlayerSpecificAlgebraicDescriptorShift
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def row (root : Candidate) (s : Data) (a : FixedArrayTable 3 Data) : FixedArrayTable 3 Data :=
  FixedArrayTable.ofFn (fun j => if j=2 then PlayerSpecificAlgebraicField.plus root.polynomial (a.read j) s else a.read j)

def shift {slots : ℕ} (root : Candidate) (s : Data) (d : Descriptor 3 slots) : Descriptor 3 slots :=
  ⟨d.weights,FixedArrayTable.ofFn (fun slot => row root s (d.first.read slot)),
    FixedArrayTable.ofFn (fun slot => row root s (d.second.read slot))⟩

theorem row_value (root : Candidate) (s : Data) (a : FixedArrayTable 3 Data) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) : values (row root s a) x=shiftThird (realEvaluate s x) (values a x) := by
  funext j
  fin_cases j <;> simp [row,values,FixedArrayTable.read_ofFn,shiftThird,PlayerSpecificAlgebraicField.plus_value _ _ _ x hx]

theorem fields {slots : ℕ} (root : Candidate) (s : Data) (d : Descriptor 3 slots) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) :
    (shift root s d).weights=d.weights ∧
      (∀ slot,values ((shift root s d).first.read slot) x=shiftThird (realEvaluate s x) (values (d.first.read slot) x)) ∧
      (∀ slot,values ((shift root s d).second.read slot) x=shiftThird (realEvaluate s x) (values (d.second.read slot) x)) := by
  refine ⟨rfl,?_,?_⟩
  · intro slot; rw [shift,FixedArrayTable.read_ofFn]; exact row_value root s _ x hx
  · intro slot; rw [shift,FixedArrayTable.read_ofFn]; exact row_value root s _ x hx

theorem row_bounds (root : Candidate) (s : Data) (a : FixedArrayTable 3 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hs : Reduced root.polynomial s ∧ HasHeight s T)
    (ha : ∀ j,Reduced root.polynomial (a.read j) ∧ HasHeight (a.read j) T) :
    ∀ j,Reduced root.polynomial ((row root s a).read j) ∧ HasHeight ((row root s a).read j) (step T) := by
  have ht : T≤step T := (Nat.le_succ _).trans (large T)
  have hshort : T+T+1≤step T := by
    have h:=calibrate 3 T (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  intro j
  rw [row,FixedArrayTable.read_ofFn]
  split
  · exact ⟨PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0,
      mono (PlayerSpecificShortReduction.plus_height _ _ _ hm hm0 (ha j).1 hs.1 T T (ha j).2 hs.2) hshort⟩
  · exact ⟨(ha j).1,mono (ha j).2 ht⟩

theorem bounds {slots : ℕ} (root : Candidate) (s : Data) (d : Descriptor 3 slots) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hs : Reduced root.polynomial s ∧ HasHeight s T) (hd : Bounds root d T) : Bounds root (shift root s d) (step T) := by
  constructor
  · intro slot
    exact ⟨(hd.weights slot).1,mono (hd.weights slot).2 ((Nat.le_succ _).trans (large T))⟩
  · intro slot j
    rw [shift,FixedArrayTable.read_ofFn]
    exact row_bounds root s _ T hm hm0 hs (hd.first slot) j
  · intro slot j
    rw [shift,FixedArrayTable.read_ofFn]
    exact row_bounds root s _ T hm hm0 hs (hd.second slot) j

end Blotto.PlayerSpecificAlgebraicDescriptorShift
