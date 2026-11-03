import Blotto.BinaryQuadraticExpressionMeasured
import Blotto.BinaryFourOrderLifetime

/-! Three reached measured comparisons produce the actual sorting permutation
and ordered four-variable record. Preceding full data/trace is preserved.
Permutation/record work reserves source control; native observers/references
and allocator realization remain separate. -/

namespace Blotto.BinaryFourOrderMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryFourSpecSampler
set_option autoImplicit false
set_option maxHeartbeats 3000000

def compare (length : Fin 3 → SignedWord) (i j : Fin 3) : (Equiv.Perm (Fin 3) × Trace) × ℕ :=
  let compared := BinaryQuadraticExpressionMeasured.compare (length i) (length j)
  ((if compared.1.1 then Equiv.refl _ else Equiv.swap i j,wrap 16 2 [compared.1.2]),compared.2+4)

theorem compare_erases (length : Fin 3 → SignedWord) (i j : Fin 3) :
    (compare length i j).1 = BinaryFourOrderLifetime.compareWithTrace length i j := by
  simp only [compare,BinaryFourOrderLifetime.compareWithTrace,BinaryQuadraticExpressionMeasured.compare_erases]

def sort (length : Fin 3 → SignedWord) : (Equiv.Perm (Fin 3) × Trace) × ℕ :=
  let first := compare length 0 1
  let middle := fun j => length (first.1.1 j)
  let second := compare middle 1 2
  let last := fun j => middle (second.1.1 j)
  let third := compare last 0 1
  (((third.1.1.trans second.1.1).trans first.1.1,wrap 32 3 [first.1.2,second.1.2,third.1.2]),
    first.2+second.2+third.2+8)

theorem sort_erases (length : Fin 3 → SignedWord) :
    (sort length).1 = BinaryFourOrderLifetime.sortWithTrace length := by
  simp only [sort,BinaryFourOrderLifetime.sortWithTrace,compare_erases]

def ordered (input : Input) : ((BinaryFourParameters.Input × Equiv.Perm (Fin 4)) × Trace) × ℕ :=
  let sorted := sort input.length.read
  (((⟨input.B,input.length.read (sorted.1.1 0),input.length.read (sorted.1.1 1),input.length.read (sorted.1.1 2),input.ell,input.p⟩,
    (rationalPermutationWithLast sorted.1.1).symm),wrap 64 4 [sorted.1.2]),sorted.2+8)

theorem ordered_erases (input : Input) : (ordered input).1 = BinaryFourOrderLifetime.orderedWithTrace input := by
  simp only [ordered,BinaryFourOrderLifetime.orderedWithTrace,sort_erases]

def workEnvelope (s : ℕ) : ℕ := 3*BinaryQuadraticExpression.uniformPrice s+28

theorem compare_work (length : Fin 3 → SignedWord) (hC : ∀ j,CanonicalWord (length j))
    (s : ℕ) (hH : ∀ j,RationalHeight (value (length j)) s) (i j : Fin 3) :
    (compare length i j).2 ≤ BinaryQuadraticExpression.uniformPrice s+4 := by
  have hI := (hC i).2.trans (rationalWordWidth_of_height (hH i))
  have hJ := (hC j).2.trans (rationalWordWidth_of_height (hH j))
  have h := BinaryQuadraticExpression.comparePrice_bound (length i) (length j) s (by omega) (by omega)
  simp only [compare,BinaryQuadraticExpressionMeasured.compare_work]
  omega

theorem sort_work (length : Fin 3 → SignedWord) (hC : ∀ j,CanonicalWord (length j))
    (s : ℕ) (hH : ∀ j,RationalHeight (value (length j)) s) :
    (sort length).2 ≤ 3*BinaryQuadraticExpression.uniformPrice s+20 := by
  let first := compare length 0 1
  let middle := fun j => length (first.1.1 j)
  let second := compare middle 1 2
  let last := fun j => middle (second.1.1 j)
  have hFirst := compare_work length hC s hH 0 1
  have hSecond := compare_work middle (fun _ => hC _) s (fun _ => hH _) 1 2
  have hThird := compare_work last (fun _ => hC _) s (fun _ => hH _) 0 1
  change first.2 ≤ _ at hFirst
  change second.2 ≤ _ at hSecond
  change first.2+second.2+(compare last 0 1).2+8 ≤ _
  omega

theorem ordered_work (input : Input) (hC : input.Canonical) (s : ℕ)
    (hH : ∀ j,RationalHeight (value (input.length.read j)) s) : (ordered input).2 ≤ workEnvelope s := by
  have h := sort_work input.length.read hC.2.1 s hH
  change _+8 ≤ _
  unfold workEnvelope
  omega

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ)
    (hH : ∀ j,RationalHeight (value (input.length.read j)) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (ordered input).1.2 steps ≤ borrowed+BinaryFourOrderLifetime.orderedEnvelope s ∧
      framePeak ((ordered input).1.2.take steps) ≤ BinaryFourOrderLifetime.orderedEnvelope s := by
  rw [ordered_erases]
  exact BinaryFourOrderLifetime.all_prefix input hC s hH borrowed steps

end Blotto.BinaryFourOrderMeasured
