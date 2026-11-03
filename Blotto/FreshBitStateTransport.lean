import Blotto.SequentialFairBitSource
import Blotto.BinaryReturnedFactoryExtras

/-! A commuting primitive-state map preserves the complete actual generation
record, including its returned plan, trace and work. No fairness premise is
used in this deterministic representation transport. -/
namespace Blotto.FreshBitStateTransport
open BinarySeedPreparationSpace BinaryTracePlanMeasured
set_option autoImplicit false
set_option maxHeartbeats 2000000

def mapBlock {S : Type*} {T : Type*} {D : Type*} (f : S → T)
    (out : ((List Bool × S) × D) × ℕ) : ((List Bool × T) × D) × ℕ :=
  (((out.1.1.1,f out.1.1.2),out.1.2),out.2)

def mapEmission {S : Type*} {T : Type*} (f : S → T)
    (out : (((List Bool × S) × Trace) × ℕ) × ℕ) : (((List Bool × T) × Trace) × ℕ) × ℕ :=
  (mapBlock f out.1,out.2)

theorem loopPlan {S : Type*} {T : Type*} (nextS : S → Bool × S) (nextT : T → Bool × T)
    (f : S → T) (hNext : ∀ state,nextT (f state) = ((nextS state).1,f (nextS state).2))
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    BinaryFreshGenerationPlan.loopPlanAt nextT counter reversed (f state) depth =
      mapBlock f (BinaryFreshGenerationPlan.loopPlanAt nextS counter reversed state depth) := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S) (depth : ℕ),
      BinaryFreshGenerationPlan.loopPlanAt nextT counter reversed (f state) depth =
        mapBlock f (BinaryFreshGenerationPlan.loopPlanAt nextS counter reversed state depth) := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state depth
        conv_lhs => rw [BinaryFreshGenerationPlan.loopPlanAt]
        conv_rhs => arg 2; rw [BinaryFreshGenerationPlan.loopPlanAt]
        by_cases hTest : (BooleanFreshSeedMeasured.scanAt counter (depth+2)).1.1 = true
        · have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [BooleanFreshSeedMeasured.scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hData : (BooleanFreshSeedMeasured.predecessorAt counter (depth+2)).1.1 =
              BinaryStoredCountdown.predecessor counter := by
            rw [BooleanFreshSeedMeasured.predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          have hLess : BinaryBigEndian.littleValue (BooleanFreshSeedMeasured.predecessorAt counter (depth+2)).1.1 < count := by
            rw [hData]; omega
          have hi := ih _ hLess _ rfl ((nextS state).1::reversed) (nextS state).2 (depth+2)
          simp only [dite_eq_left hTest,hNext,mapBlock]
          rw [hi]
          rfl
        · simp only [dite_eq_right hTest,mapBlock]
  exact hAll _ counter rfl reversed state depth

theorem generatePlan {S : Type*} {T : Type*} {n : ℕ}
    (nextS : S → Bool × S) (nextT : T → Bool × T) (f : S → T)
    (hNext : ∀ state,nextT (f state) = ((nextS state).1,f (nextS state).2))
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    BinaryFreshGenerationPlan.generatePlan nextT request (f state) =
      mapBlock f (BinaryFreshGenerationPlan.generatePlan nextS request state) := by
  simp only [BinaryFreshGenerationPlan.generatePlan,loopPlan nextS nextT f hNext,mapBlock]

theorem generate {S : Type*} {T : Type*} {n : ℕ}
    (nextS : S → Bool × S) (nextT : T → Bool × T) (f : S → T)
    (hNext : ∀ state,nextT (f state) = ((nextS state).1,f (nextS state).2))
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    BinaryFreshGenerationPlan.generateWithEmission nextT request (f state) =
      mapEmission f (BinaryFreshGenerationPlan.generateWithEmission nextS request state) := by
  simp only [BinaryFreshGenerationPlan.generateWithEmission,generatePlan nextS nextT f hNext,mapBlock,mapEmission]

def mapLeft {A : Type*} {B : Type*} {C : Type*} (f : A → B) (out : A × C) : B × C :=
  (f out.1,out.2)

def mapState {S : Type*} {T : Type*} {A : Type*} {G1 : Type*} {G2 : Type*} {G3 : Type*} {G4 : Type*} {G5 : Type*} {G6 : Type*} {G7 : Type*} {G8 : Type*} {G9 : Type*} {G10 : Type*} (f : S → T) (out : (((((((((((A × S) × G1) × G2) × G3) × G4) × G5) × G6) × G7) × G8) × G9) × G10)) : (((((((((((A × T) × G1) × G2) × G3) × G4) × G5) × G6) × G7) × G8) × G9) × G10) :=
  (mapLeft (mapLeft (mapLeft (mapLeft (mapLeft (mapLeft (mapLeft (mapLeft (mapLeft (mapLeft (fun p : A × S => (p.1,f p.2)))))))))))) out

variable {E : Type*} [Zero E] [Add E]

theorem generated {S : Type*} {T : Type*} (backend : BinaryRawParserContinuation.Backend E)
    (nextS : S → Bool × S) (nextT : T → Bool × T) (f : S → T)
    (hNext : ∀ state,nextT (f state) = ((nextS state).1,f (nextS state).2))
    (rich : Bool) (frame : List Bool) (state : S) :
    BinaryRawParserContinuation.generatedWithFactoryExtras backend nextT rich frame (f state) =
      mapState f (BinaryRawParserContinuation.generatedWithFactoryExtras backend nextS rich frame state) := by
  unfold BinaryRawParserContinuation.generatedWithFactoryExtras
  dsimp only
  split
  · rfl
  · split
    · simp only [generate nextS nextT f hNext,mapEmission,mapBlock,mapState,mapLeft]
    · rfl

theorem parsedGenerated {S : Type*} {T : Type*} (backend : BinaryRawParserContinuation.Backend E)
    (nextS : S → Bool × S) (nextT : T → Bool × T) (f : S → T)
    (hNext : ∀ state,nextT (f state) = ((nextS state).1,f (nextS state).2))
    (rich : Bool) (frame : List Bool) (state : S) :
    BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend nextT rich frame (f state) =
      mapState f (BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras backend nextS rich frame state) := by
  unfold BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras
  dsimp only
  split
  · rfl
  · split
    · simp only [generate nextS nextT f hNext,mapEmission,mapBlock,mapState,mapLeft]
    · rfl

attribute [local irreducible] BinaryRawParserContinuation.generatedWithFactoryExtras BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras

theorem pair {S : Type*} {T : Type*} (backend : BinaryRawParserContinuation.Backend E)
    (nextS : S → Bool × S) (nextT : T → Bool × T) (f : S → T)
    (hNext : ∀ state,nextT (f state) = ((nextS state).1,f (nextS state).2))
    (frame : List Bool) (state : S) :
    BinaryRawParserContinuation.pairWithFactoryExtras backend nextT frame (f state) =
      mapState f (BinaryRawParserContinuation.pairWithFactoryExtras backend nextS frame state) := by
  simp only [BinaryRawParserContinuation.pairWithFactoryExtras,generated backend nextS nextT f hNext,mapState,mapLeft]

theorem parsedPair {S : Type*} {T : Type*} (backend : BinaryRawParserContinuation.Backend E)
    (nextS : S → Bool × S) (nextT : T → Bool × T) (f : S → T)
    (hNext : ∀ state,nextT (f state) = ((nextS state).1,f (nextS state).2))
    (frame : List Bool) (state : S) :
    BinaryRawParserContinuation.parsedPairWithFactoryExtras backend nextT frame (f state) =
      mapState f (BinaryRawParserContinuation.parsedPairWithFactoryExtras backend nextS frame state) := by
  simp only [BinaryRawParserContinuation.parsedPairWithFactoryExtras,parsedGenerated backend nextS nextT f hNext,mapState,mapLeft]


end Blotto.FreshBitStateTransport
