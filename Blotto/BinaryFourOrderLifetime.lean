import Blotto.BinaryThreeGeometryLifetime
import Blotto.BinaryFourNativeOrderWork

/-! Three actual quadratic comparisons sort the three free coordinates of the
four-variable input. The selected permutations and ordered record feed later
producers. Original signed words are borrowed; comparison and record regions
remain retained. -/
namespace Blotto.BinaryFourOrderLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFourSpecSampler
set_option maxHeartbeats 2000000

def compareWithTrace (length : Fin 3 → SignedWord) (i j : Fin 3) : Equiv.Perm (Fin 3) × Trace :=
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace (length i) (length j)
  (if compared.1 then Equiv.refl _ else Equiv.swap i j,wrap 16 2 [compared.2])

theorem compareWithTrace_erasure (length : Fin 3 → SignedWord) (i j : Fin 3) :
    (compareWithTrace length i j).1 = BinaryFourSpecSampler.comparePermutation length i j := by
  unfold compareWithTrace BinaryFourSpecSampler.comparePermutation
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]

def sortWithTrace (length : Fin 3 → SignedWord) : Equiv.Perm (Fin 3) × Trace :=
  let first := compareWithTrace length 0 1
  let middle := fun j => length (first.1 j)
  let second := compareWithTrace middle 1 2
  let last := fun j => middle (second.1 j)
  let third := compareWithTrace last 0 1
  ((third.1.trans second.1).trans first.1,wrap 32 3 [first.2,second.2,third.2])

theorem sortWithTrace_erasure (length : Fin 3 → SignedWord) :
    (sortWithTrace length).1 = BinaryFourSpecSampler.sortPermutation length := by
  unfold sortWithTrace BinaryFourSpecSampler.sortPermutation
  simp only [compareWithTrace_erasure]

def orderedWithTrace (input : Input) :
    (BinaryFourParameters.Input × Equiv.Perm (Fin 4)) × Trace :=
  let sorted := sortWithTrace input.length.read
  ((⟨input.B,input.length.read (sorted.1 0),input.length.read (sorted.1 1),input.length.read (sorted.1 2),input.ell,input.p⟩,
    (rationalPermutationWithLast sorted.1).symm),wrap 64 4 [sorted.2])

theorem orderedWithTrace_erasure (input : Input) :
    (orderedWithTrace input).1 = (orderedInput input,permutation input) := by
  unfold orderedWithTrace orderedInput permutation
  simp only [sortWithTrace_erasure]

def compareEnvelope (s : ℕ) : ℕ := BinaryThreeGeometryLifetime.comparisonEnvelope (2 * s + 1) + 24
def sortEnvelope (s : ℕ) : ℕ := 3 * compareEnvelope s + 48
def orderedEnvelope (s : ℕ) : ℕ := sortEnvelope s + 72

theorem compareWithTrace_usage (length : Fin 3 → SignedWord) (hC : ∀ j,CanonicalWord (length j))
    (s : ℕ) (hHeight : ∀ j,RationalHeight (value (length j)) s) (i j : Fin 3) :
    usage (compareWithTrace length i j).2 ≤ compareEnvelope s := by
  have hI : width (length i) ≤ 2 * s + 1 := by
    have h := (hC i).2.trans (rationalWordWidth_of_height (hHeight i))
    omega
  have hJ : width (length j) ≤ 2 * s + 1 := by
    have h := (hC j).2.trans (rationalWordWidth_of_height (hHeight j))
    omega
  have hc := BinaryThreeGeometryLifetime.comparison_usage (length i) (length j) (2 * s + 1) hI hJ
  have hw := wrap_usage 16 2 [(BinaryQuadraticExpressionLifetime.compareWithTrace (length i) (length j)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 16 2 [(BinaryQuadraticExpressionLifetime.compareWithTrace (length i) (length j)).2]) ≤ _
  unfold compareEnvelope
  omega

theorem sortWithTrace_usage (length : Fin 3 → SignedWord) (hC : ∀ j,CanonicalWord (length j))
    (s : ℕ) (hHeight : ∀ j,RationalHeight (value (length j)) s) :
    usage (sortWithTrace length).2 ≤ sortEnvelope s := by
  let first := compareWithTrace length 0 1
  let middle := fun j => length (first.1 j)
  let second := compareWithTrace middle 1 2
  let last := fun j => middle (second.1 j)
  let third := compareWithTrace last 0 1
  have hFirst := compareWithTrace_usage length hC s hHeight 0 1
  have hSecond := compareWithTrace_usage middle (fun j => hC _) s (fun j => hHeight _) 1 2
  have hThird := compareWithTrace_usage last (fun j => hC _) s (fun j => hHeight _) 0 1
  change usage first.2 ≤ _ at hFirst
  change usage second.2 ≤ _ at hSecond
  change usage third.2 ≤ _ at hThird
  have hw := wrap_usage 32 3 [first.2,second.2,third.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 3 [first.2,second.2,third.2]) ≤ _
  unfold sortEnvelope
  omega

theorem orderedWithTrace_usage (input : Input) (hC : input.Canonical) (s : ℕ)
    (hHeight : ∀ j,RationalHeight (value (input.length.read j)) s) :
    usage (orderedWithTrace input).2 ≤ orderedEnvelope s := by
  have hSort := sortWithTrace_usage input.length.read hC.2.1 s hHeight
  have hw := wrap_usage 64 4 [(sortWithTrace input.length.read).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 4 [(sortWithTrace input.length.read).2]) ≤ _
  unfold orderedEnvelope
  omega

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ)
    (hHeight : ∀ j,RationalHeight (value (input.length.read j)) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (orderedWithTrace input).2 steps ≤ borrowed + orderedEnvelope s ∧
      framePeak ((orderedWithTrace input).2.take steps) ≤ orderedEnvelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (orderedWithTrace_usage input hC s hHeight) borrowed steps

end Blotto.BinaryFourOrderLifetime
