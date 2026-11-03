import Blotto.BinaryWordGroupEmissionMeasured
import Blotto.BinaryWordTerminalLifetime

/-! Complete cached terminal dispatch adopts measured route emission for the
uniform, mixed-two and mixed-three branches. Data and cursor equal the selected
old terminal, while the new traces have additive polynomial growth. The work
field prices emission and wrapper/dispatch control only; actual factory/draw
work and native model realization remain separate. No SmallBranch restriction. -/

namespace Blotto.BinaryWordTerminalEmissionMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedTerminalPreparation BinaryCachedThreeDescriptorWork BinaryGroupInputs BinaryGroupSamplers
open BinaryMeasuredEmissionGrowth
set_option autoImplicit false
set_option maxHeartbeats 3500000

def branch {α : Type*} (drawn : (α × Trace) × ℕ) : (α × Trace) × ℕ :=
  ((drawn.1.1,wrap 24 2 [wrap 32 2 [drawn.1.2]]),drawn.2+16)

theorem branch_growth {α : Type*} (before : Trace) (after : (α × Trace) × ℕ) (D : ℕ)
    (h : Growth before after.1.2 D) :
    Growth (wrap 24 2 [wrap 32 2 [before]]) (branch after).1.2 (D+2+2) :=
  wrap_one 24 2 _ _ _ (wrap_one 32 2 _ _ _ h)

def drawTwo {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedTwoRun store input hC hAd routes pivot K scalar pc hp

theorem drawTwo_data {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawTwo store input hC hAd hTwo routes pivot K scalar pc hp).1.1 =
      (BinaryWordMixedTwoTerminalLifetime.drawWithTrace store input hC hAd hTwo routes pivot K scalar pc hp).1 := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedTwoRun_data store input hC hAd routes pivot K scalar pc hp

theorem drawTwo_growth {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Growth (BinaryWordMixedTwoTerminalLifetime.drawWithTrace store input hC hAd hTwo routes pivot K scalar pc hp).2
      (drawTwo store input hC hAd hTwo routes pivot K scalar pc hp).1.2 (mixedDelta n 2+4) := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedTwoRun_growth store input hC hAd routes pivot K scalar pc hp

theorem drawTwo_work {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : MixedHeights input s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawTwo store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤ BinaryWordGroupEmissionMeasured.mixedWork n 2 s K := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedTwoRun_work store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K scalar pc hp

def drawThree {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp

theorem drawThree_data {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThree store input hC hAd hThree routes pivot K outer scalar pc hp).1.1 =
      (BinaryWordMixedThreeTerminalLifetime.drawWithTrace store input hC hAd hThree routes pivot K outer scalar pc hp).1 := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedThreeRun_data store input hC hAd routes pivot K outer scalar pc hp

theorem drawThree_growth {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Growth (BinaryWordMixedThreeTerminalLifetime.drawWithTrace store input hC hAd hThree routes pivot K outer scalar pc hp).2
      (drawThree store input hC hAd hThree routes pivot K outer scalar pc hp).1.2 (mixedDelta n 3+4) := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedThreeRun_growth store input hC hAd routes pivot K outer scalar pc hp

theorem drawThree_work {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : MixedHeights input s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThree store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤ BinaryWordGroupEmissionMeasured.mixedWork n 3 s K := by
  subst m
  exact BinaryWordGroupEmissionMeasured.mixedThreeRun_work store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K outer scalar pc hp

def run {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  match hPivot : prepared.pivot with
  | none => branch (BinaryWordGroupEmissionMeasured.uniformRun store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp)
  | some selected =>
      if hTwo : prepared.count = 2 then
        branch (drawTwo store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          hTwo prepared.routes selected K scalar pc hp)
      else
        branch (drawThree store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp)

theorem run_data {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared hC hAd K outer scalar pc hp).1.1 =
      (BinaryWordTerminalLifetime.runWithTrace store prepared hC hAd K outer scalar pc hp).1 := by
  rw [BinaryWordTerminalLifetime.runWithTrace_erasure]
  unfold run
  split
  · rename_i hPivot
    exact (BinaryWordGroupEmissionMeasured.uniformRun_data store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp).trans
      (BinaryWordUniformTerminalLifetime.runWithTrace_erasure store prepared hC hAd hPivot K outer scalar pc hp)
  · rename_i selected hPivot
    split
    · rename_i hTwo
      exact (drawTwo_data store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected K scalar pc hp).trans
        (BinaryWordMixedTwoTerminalLifetime.runWithTrace_erasure store prepared hC hAd hTwo selected hPivot K outer scalar pc hp)
    · rename_i hTwo
      exact (drawThree_data store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp).trans
        (BinaryWordMixedThreeTerminalLifetime.runWithTrace_erasure store prepared hC hAd
          ((prepared.count_bound hC hAd).resolve_left hTwo) selected hPivot K outer scalar pc hp)

theorem reference_uniform_trace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hPivot : prepared.pivot = none) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalLifetime.runWithTrace store prepared hC hAd K outer scalar pc hp).2 =
      wrap 24 2 [(BinaryWordUniformTerminalLifetime.runWithTrace store prepared hC hAd hPivot K scalar pc hp).2] := by
  unfold BinaryWordTerminalLifetime.runWithTrace
  dsimp only
  split
  · rfl
  · rename_i selected hOther
    cases hPivot.symm.trans hOther

theorem reference_two_trace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hTwo : prepared.count = 2) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalLifetime.runWithTrace store prepared hC hAd K outer scalar pc hp).2 =
      wrap 24 2 [(BinaryWordMixedTwoTerminalLifetime.runWithTrace store prepared hC hAd hTwo selected hPivot K scalar pc hp).2] := by
  unfold BinaryWordTerminalLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    cases hPivot.symm.trans hNone
  · rename_i other hOther
    have he := Option.some.inj (hPivot.symm.trans hOther)
    subst other
    split
    · rfl
    · rename_i hNot
      exact False.elim (hNot hTwo)

theorem reference_three_trace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hNot : prepared.count ≠ 2) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalLifetime.runWithTrace store prepared hC hAd K outer scalar pc hp).2 =
      wrap 24 2 [(BinaryWordMixedThreeTerminalLifetime.runWithTrace store prepared hC hAd
        ((prepared.count_bound hC hAd).resolve_left hNot) selected hPivot K outer scalar pc hp).2] := by
  unfold BinaryWordTerminalLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    cases hPivot.symm.trans hNone
  · rename_i other hOther
    have he := Option.some.inj (hPivot.symm.trans hOther)
    subst other
    split
    · rename_i hTwo
      exact False.elim (hNot hTwo)
    · rfl

def delta (n : ℕ) : ℕ := arrayDelta n+mixedDelta n 3+16

theorem run_growth {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Growth (BinaryWordTerminalLifetime.runWithTrace store prepared hC hAd K outer scalar pc hp).2
      (run store prepared hC hAd K outer scalar pc hp).1.2 (delta n) := by
  unfold run
  split
  · rename_i hPivot
    rw [reference_uniform_trace store prepared hC hAd hPivot K outer scalar pc hp]
    have h := branch_growth _ _ _ (BinaryWordGroupEmissionMeasured.uniformRun_growth store prepared.uniform
      (prepared.uniform_canonical hC) (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp)
    exact growth_mono _ _ _ _ h (by unfold delta; omega)
  · rename_i selected hPivot
    split
    · rename_i hTwo
      rw [reference_two_trace store prepared hC hAd hTwo selected hPivot K outer scalar pc hp]
      have h := branch_growth _ _ _ (drawTwo_growth store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected K scalar pc hp)
      have hm := mixedDelta_mono n 2 3 (by decide)
      exact growth_mono _ _ _ _ h (by unfold delta; omega)
    · rename_i hNot
      rw [reference_three_trace store prepared hC hAd hNot selected hPivot K outer scalar pc hp]
      have h := branch_growth _ _ _ (drawThree_growth store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hNot) prepared.routes selected K outer scalar pc hp)
      exact growth_mono _ _ _ _ h (by unfold delta; omega)

def workEnvelope (n s K : ℕ) : ℕ := BinaryWordGroupEmissionMeasured.uniformWork n s K+
  BinaryWordGroupEmissionMeasured.mixedWork n 2 s K+BinaryWordGroupEmissionMeasured.mixedWork n 3 s K+32

theorem run_work {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared hC hAd K outer scalar pc hp).2 ≤ workEnvelope n s K := by
  have hRC := BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC
  unfold run
  split
  · rename_i hPivot
    have h := BinaryWordGroupEmissionMeasured.uniformRun_work store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes hRC s hs hUniform hRoutes K scalar pc hp
    change _+16 ≤ _
    unfold workEnvelope
    omega
  · rename_i selected hPivot
    split
    · rename_i hTwo
      have h := drawTwo_work store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected hRC s hs (hMixed selected hPivot) hRoutes K scalar pc hp
      change _+16 ≤ _
      unfold workEnvelope
      omega
    · rename_i hNot
      have h := drawThree_work store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hNot) prepared.routes selected hRC s hs
        (hMixed selected hPivot) hRoutes K outer scalar pc hp
      change _+16 ≤ _
      unfold workEnvelope
      omega

theorem run_usage {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (run store prepared hC hAd K outer scalar pc hp).1.2 ≤
      BinaryWordTerminalLifetime.envelope n s K store.width store.cap.value (store.cap.value-pc.value)+2*delta n := by
  have ho := BinaryWordTerminalLifetime.runWithTrace_usage store prepared hC hAd s hs hUniform hMixed hRoutes K outer scalar pc hp
  have hg := usage_growth _ _ _ (run_growth store prepared hC hAd K outer scalar pc hp)
  omega

theorem run_position {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store prepared hC hAd K outer scalar pc hp).1.1.2.value ∧
      (run store prepared hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryWordTerminalLifetime.runWithTrace_position store prepared hC hAd K outer scalar pc hp

theorem delta_polynomial (n : ℕ) : delta n ≤ 2048*(n+4)^2 := by
  have ha := arrayDelta_polynomial n
  have hm := mixedDelta_polynomial n 3
  have hp : (n+1)^2 ≤ (n+4)^2 := Nat.pow_le_pow_left (by omega) 2
  unfold delta
  nlinarith

theorem work_mono {n s K N S T : ℕ} (hn : n ≤ N) (hs : s ≤ S) (hK : K ≤ T) :
    workEnvelope n s K ≤ workEnvelope N S T := by
  unfold workEnvelope BinaryWordGroupEmissionMeasured.uniformWork BinaryWordGroupEmissionMeasured.mixedWork
    BinaryGroupEmissionMeasured.mixedWorkEnvelope BinaryGroupEmissionMeasured.workEnvelope
    BinaryWordGroupEmissionLifetime.groupHeight expressionHeightBudget
  gcongr

theorem work_diagonal : NaturalPolynomialEnvelope BinaryPRGHeapResourcePolynomial.inputSize
    (fun p => workEnvelope p.wordWidth p.wordWidth p.wordWidth) := by
  unfold workEnvelope BinaryWordGroupEmissionMeasured.uniformWork BinaryWordGroupEmissionMeasured.mixedWork
    BinaryGroupEmissionMeasured.mixedWorkEnvelope BinaryGroupEmissionMeasured.workEnvelope
    BinaryWordGroupEmissionLifetime.groupHeight expressionHeightBudget
  resource_polynomial

theorem work_polynomial : ∃ C d : ℕ, ∀ n s K,workEnvelope n s K ≤ C*(n+s+K+2)^d := by
  obtain ⟨C,d,hBound⟩ := work_diagonal
  refine ⟨C,d,?_⟩
  intro n s K
  let T := n+s+K
  have hMono : workEnvelope n s K ≤ workEnvelope T T T := work_mono
    (by dsimp only [T]; omega) (by dsimp only [T]; omega) (by dsimp only [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize ⟨0,T,0,0,0⟩+1 = T+2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hMono.trans h

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run store prepared hC hAd K outer scalar pc hp).1.2 steps ≤
      borrowed+(BinaryWordTerminalLifetime.envelope n s K store.width store.cap.value (store.cap.value-pc.value)+2*delta n) ∧
    framePeak ((run store prepared hC hAd K outer scalar pc hp).1.2.take steps) ≤
      BinaryWordTerminalLifetime.envelope n s K store.width store.cap.value (store.cap.value-pc.value)+2*delta n :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (run_usage store prepared hC hAd s hs hUniform hMixed hRoutes K outer scalar pc hp) borrowed steps

end Blotto.BinaryWordTerminalEmissionMeasured
