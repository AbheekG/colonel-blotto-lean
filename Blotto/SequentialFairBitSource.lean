import Blotto.FreshBitSeedKernel
import Blotto.BinaryFreshGenerationPlan

/-! A sequential Boolean-tape provider has no numerical position counter or
indexing operation. Its data semantics is total; the independent fair law is
proved for the fixed finite fair-tape interpretation, not supplied by a caller.
This does not assign native pointer/constructor/allocator unit prices. -/
namespace Blotto.SequentialFairBitSource
open FreshBitSeedLifetime
open BinarySeedPreparationSpace RationalLottoResourceSystem
set_option autoImplicit false
set_option maxHeartbeats 1500000

def next : List Bool → Bool × List Bool
  | [] => (false,[])
  | bit::rest => (bit,rest)

def run (count : ℕ) (tape : List Bool) : (List Bool × List Bool) × Trace :=
  generateWithTrace next count tape

def pair (R S : ℕ) (tape : List Bool) : (List Bool × List Bool) × List Bool :=
  let first := run R tape
  let second := run S first.1.2
  ((first.1.1,second.1.1),second.1.2)

theorem next_remaining (tape : List Bool) : (next tape).2 = tape.tail := by
  cases tape <;> rfl

theorem next_length (tape : List Bool) : (next tape).2.length ≤ tape.length := by
  cases tape <;> simp [next]

theorem next_drop (tape : List Bool) (position : ℕ) :
    next (tape.drop position) = (tape.getD position false,tape.drop (position+1)) := by
  induction position generalizing tape with
  | zero => cases tape <;> rfl
  | succ position ih => cases tape with
    | nil => simp [next]
    | cons bit rest => simpa only [List.drop_succ_cons,List.getD_cons_succ] using ih rest

theorem loop_prefix (front suffix reversed : List Bool) :
    (loopWithTrace next front.length reversed (front++suffix)).1 =
      (reversed.reverse++front,suffix) := by
  induction front generalizing reversed with
  | nil => simp [loopWithTrace,BinarySeedPreparationSpace.reverseWithTrace_result,List.reverseAux_eq]
  | cons bit rest ih =>
      simp only [List.length_cons,List.cons_append,loopWithTrace,next]
      rw [ih]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem run_prefix (front suffix : List Bool) :
    (run front.length (front++suffix)).1 = (front,suffix) := by
  simpa only [run,generateWithTrace,List.reverse_nil,List.nil_append] using loop_prefix front suffix []

theorem run_enough (count : ℕ) (tape : List Bool) (h : count ≤ tape.length) :
    (run count tape).1 = (tape.take count,tape.drop count) := by
  have hl : (tape.take count).length = count := List.length_take_of_le h
  have he := run_prefix (tape.take count) (tape.drop count)
  simpa only [hl,List.take_append_drop] using he

theorem loop_remaining (count : ℕ) (reversed tape : List Bool) :
    (loopWithTrace next count reversed tape).1.2 = tape.drop count := by
  induction count generalizing reversed tape with
  | zero => rfl
  | succ count ih => cases tape <;> simp only [loopWithTrace,next,ih,List.drop_nil,List.drop_succ_cons]

theorem run_remaining (count : ℕ) (tape : List Bool) :
    (run count tape).1.2 = tape.drop count := loop_remaining count [] tape

theorem run_vector {N : ℕ} (bits : Fin N → Bool) :
    (run N (List.ofFn bits)).1 = (List.ofFn bits,[]) := by
  have h := run_prefix (List.ofFn bits) []
  simpa only [List.length_ofFn,List.append_nil] using h

theorem run_length (count : ℕ) (tape : List Bool) : (run count tape).1.1.length = count :=
  generate_length next count tape

theorem run_counted (count : ℕ) (tape : List Bool) (calls : ℕ) :
    (generateWithTrace (countedFresh next) count (tape,calls)).1 =
      ((run count tape).1.1,((run count tape).1.2,calls+count)) :=
  generate_counted next count tape calls

theorem pair_prefix (first second suffix : List Bool) :
    pair first.length second.length (first++second++suffix) = ((first,second),suffix) := by
  simp only [pair,List.append_assoc,run_prefix]


theorem block_list (R S : ℕ) (bits : Fin (R+S) → Bool) :
    List.ofFn bits = List.ofFn (firstBitBlock R S bits)++List.ofFn (secondBitBlock R S bits) := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  exact Fin.addCases (fun j => (Fin.append_left (firstBitBlock R S bits) (secondBitBlock R S bits) j).symm)
    (fun j => (Fin.append_right (firstBitBlock R S bits) (secondBitBlock R S bits) j).symm) i

theorem pair_vector (R S : ℕ) (bits : Fin (R+S) → Bool) :
    pair R S (List.ofFn bits) =
      ((List.ofFn (firstBitBlock R S bits),List.ofFn (secondBitBlock R S bits)),[]) := by
  rw [block_list]
  have h := pair_prefix (List.ofFn (firstBitBlock R S bits)) (List.ofFn (secondBitBlock R S bits)) []
  simpa only [List.length_ofFn,List.append_nil] using h

theorem pair_counted (R S : ℕ) (tape : List Bool) (calls : ℕ) :
    let first := generateWithTrace (countedFresh next) R (tape,calls)
    let second := generateWithTrace (countedFresh next) S first.1.2
    second.1.2.2 = calls+R+S := by
  simp only [generate_counted]

theorem run_mean (N : ℕ) (test : List Bool → ℝ) :
    (fairBitKernel N).mean (fun bits => test (run N (List.ofFn bits)).1.1) =
      (FreshBitSeedKernel.generate N).mean test := by
  simp only [run_vector]
  exact (FreshBitSeedKernel.generate_mean N test).symm

theorem pair_mean (R S : ℕ) (test : List Bool × List Bool → ℝ) :
    (fairBitKernel (R+S)).mean (fun bits => test (pair R S (List.ofFn bits)).1) =
      (FreshBitSeedKernel.pair R S).mean test := by
  simp only [pair_vector]
  exact (FreshBitSeedKernel.pair_mean R S test).symm

theorem pair_product (R S : ℕ) (test : List Bool × List Bool → ℝ) :
    (fairBitKernel (R+S)).mean (fun bits => test (pair R S (List.ofFn bits)).1) =
      (FreshBitSeedKernel.generate R).mean (fun first =>
        (FreshBitSeedKernel.generate S).mean (fun second => test (first,second))) := by
  rw [pair_mean]
  exact FreshBitSeedKernel.pair_product R S test

theorem planned_prefix {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n)
    (front suffix : List Bool) (h : front.length = sampleBitBudget n request.request.precision) :
    (BinaryFreshGenerationPlan.generateWithEmission next request (front++suffix)).1.1.1 = (front,suffix) := by
  rw [BinaryFreshGenerationPlan.generateWithEmission_compat,BinaryPRGRulerSeedMeasured.generate_reference]
  rw [← h]
  exact run_prefix front suffix

theorem planned_remaining {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (tape : List Bool) :
    (BinaryFreshGenerationPlan.generateWithEmission next request tape).1.1.1.2 =
      tape.drop (sampleBitBudget n request.request.precision) := by
  rw [BinaryFreshGenerationPlan.generateWithEmission_compat,BinaryPRGRulerSeedMeasured.generate_reference]
  exact run_remaining _ tape

end Blotto.SequentialFairBitSource
