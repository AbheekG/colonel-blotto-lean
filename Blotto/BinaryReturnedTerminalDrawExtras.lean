import Blotto.BinaryReturnedReflectedExtras
import Blotto.BinaryWordTerminalCompleteMeasured

/-! Returned draw-normalization costs through reached four-variable, group and
terminal dispatch. Existing complete records are exact projections. Descriptor
factories, root-coin normalization, resource normalization, metadata evaluation
and full native/physical models remain separate. -/
namespace Blotto.BinaryReturnedTerminalDrawExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryCachedTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 3500000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode

theorem gluing_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourGluingDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).2 ≤
      155*(BinaryFourGluingDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).1.2 := by
  have h := BinaryReturnedCategoricalExtras.segment_bound store (BinaryFourGluingDrawMeasured.prepared input hC hAd).1.1 0 K scalar pc hp
  simp only [BinaryFourGluingDrawMeasured.runWithDrawExtras_record]
  omega

theorem small_uniform_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallUniformDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).2 ≤
      155*(BinaryFourSmallUniformDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).1.2 := by
  have h := BinaryReturnedCategoricalExtras.segment_bound store (BinaryFourSmallUniformDrawMeasured.prepared input hC hAd).1.1 0 K scalar pc hp
  simp only [BinaryFourSmallUniformDrawMeasured.runWithDrawExtras_record]
  omega

theorem after_root_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    (BinaryFourSmallMeasured.afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).2 ≤
      155*(BinaryFourSmallMeasured.afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).1.2 := by
  simp only [BinaryFourSmallMeasured.afterRootWithDrawExtras_record]
  cases h : root.1.1.1 with
  | none => dsimp only; omega
  | some branch =>
      cases branch
      · dsimp only
        have h := BinaryReturnedReflectedExtras.run_bound store input hC hAd K outer scalar root.1.1.2 hNext
        omega
      · dsimp only
        have h := small_uniform_bound store input hC hAd K scalar root.1.1.2 hNext
        omega

theorem small_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      155*(BinaryFourSmallMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryFourSmallMeasured.runWithDrawExtras_record]
  exact after_root_bound store input hC hAd K outer scalar _ (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2

theorem ordered_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourOrderedMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      155*(BinaryFourOrderedMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryFourOrderedMeasured.runWithDrawExtras_record]
  split
  · rename_i hg
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
    have h := gluing_bound store input hC (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
    dsimp only [BinaryFourOrderedMeasured.join]
    omega
  · rename_i hg
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
    have h := small_bound store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp
    dsimp only [BinaryFourOrderedMeasured.join]
    omega

theorem restore_source_dominates (store : BinarySeedLookupTree.Store) (ordered : BinaryFourRestoredMeasured.Ordered)
    (drawn : BinaryFourRestoredMeasured.Result store) :
    drawn.2 ≤ (BinaryFourRestoredMeasured.restore store ordered drawn).2 := by
  dsimp only [BinaryFourRestoredMeasured.restore]
  split <;> omega

theorem after_order_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourRestoredMeasured.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : BinaryFourRestoredMeasured.Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤
      155*(BinaryFourRestoredMeasured.afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.2 := by
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  have h := ordered_bound store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  have hw := restore_source_dominates store ordered (BinaryFourOrderedMeasured.runWithDrawExtras store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp).1
  simp only [BinaryFourRestoredMeasured.afterOrderWithDrawExtras_record]
  omega

theorem restored_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourRestoredMeasured.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      155*(BinaryFourRestoredMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryFourRestoredMeasured.runWithDrawExtras_record]
  exact after_order_bound store input hC hAd _ _ K outer scalar pc hp

theorem uniform_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp).2 ≤
      155*(BinaryWordGroupCompleteMeasured.uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp).1.2 := by
  have h := BinaryReturnedCategoricalExtras.uniform_draw_bound store input hC hAd hm K scalar pc hp
  simp only [BinaryWordGroupCompleteMeasured.uniformRunWithDrawExtras_record,BinaryWordGroupCompleteMeasured.collect]
  omega

theorem mixed_two_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp).2 ≤
      155*(BinaryWordGroupCompleteMeasured.mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp).1.2 := by
  have h := BinaryReturnedCategoricalExtras.mixed_draw_bound store input hC hAd K scalar pc hp
  simp only [BinaryWordGroupCompleteMeasured.mixedTwoRunWithDrawExtras_record,BinaryWordGroupCompleteMeasured.afterMixed_record,BinaryWordGroupCompleteMeasured.collect]
  omega

theorem mixed_three_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp).2 ≤
      155*(BinaryWordGroupCompleteMeasured.mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp).1.2 := by
  have h := restored_bound store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp
  simp only [BinaryWordGroupCompleteMeasured.mixedThreeRunWithDrawExtras_record,BinaryWordGroupCompleteMeasured.afterMixed_record,BinaryWordGroupCompleteMeasured.collect]
  omega

theorem draw_two_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤
      155*(BinaryWordTerminalCompleteMeasured.drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.2 := by
  subst m
  exact mixed_two_bound store input hC hAd routes pivot K scalar pc hp

theorem draw_three_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤
      155*(BinaryWordTerminalCompleteMeasured.drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.2 := by
  subst m
  exact mixed_three_bound store input hC hAd routes pivot K outer scalar pc hp

theorem terminal_bound {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.runWithDrawExtras store prepared hC hAd K outer scalar pc hp).2 ≤
      155*(BinaryWordTerminalCompleteMeasured.runWithDrawExtras store prepared hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryWordTerminalCompleteMeasured.runWithDrawExtras_record]
  split
  · rename_i hPivot
    have h := uniform_bound store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
    dsimp only [BinaryWordTerminalCompleteMeasured.branch]
    omega
  · rename_i selected hPivot
    split
    · rename_i hTwo
      have h := draw_two_bound store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected K scalar pc hp
      dsimp only [BinaryWordTerminalCompleteMeasured.branch]
      omega
    · rename_i hTwo
      have h := draw_three_bound store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp
      dsimp only [BinaryWordTerminalCompleteMeasured.branch]
      omega

theorem gluing_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourGluingDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).1.2+(BinaryFourGluingDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).2 ≤
      156*(BinaryFourGluingDrawMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := gluing_bound store input hC hAd K scalar pc hp
  have hw := (BinaryFourGluingDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).1
  simp only [BinaryFourGluingDrawMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem small_uniform_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallUniformDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).1.2+(BinaryFourSmallUniformDrawMeasured.runWithDrawExtras store input hC hAd K scalar pc hp).2 ≤
      156*(BinaryFourSmallUniformDrawMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := small_uniform_bound store input hC hAd K scalar pc hp
  have hw := (BinaryFourSmallUniformDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).1
  simp only [BinaryFourSmallUniformDrawMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem after_root_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value)
    (hRoot : root.2 ≤ BinaryFourSmallCoinMeasured.workEnvelope s store.width store.cap.value ∧
      usage root.1.2 ≤ BinaryFourSmallCoinLifetime.envelope s store.width store.cap.value) :
    (BinaryFourSmallMeasured.afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).1.2+(BinaryFourSmallMeasured.afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).2 ≤
      156*(BinaryFourSmallMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := after_root_bound store input hC hAd K outer scalar root hNext
  have hw := (BinaryFourSmallMeasured.afterRoot_bounds store input source hC hR hCase hAd s hs hH K outer scalar root hNext hRoot).1
  simp only [BinaryFourSmallMeasured.afterRootWithDrawExtras_compat] at he ⊢
  omega

theorem small_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourSmallMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      156*(BinaryFourSmallMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := small_bound store input hC hAd K outer scalar pc hp
  have hw := (BinaryFourSmallMeasured.run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp).1
  simp only [BinaryFourSmallMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem ordered_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourOrderedMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourOrderedMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      156*(BinaryFourOrderedMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := ordered_bound store input hC hAd K outer scalar pc hp
  have hw := (BinaryFourOrderedMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp).1
  simp only [BinaryFourOrderedMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem after_order_price (store : BinarySeedLookupTree.Store) (input : BinaryFourRestoredMeasured.Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (ordered : BinaryFourRestoredMeasured.Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (P U : ℕ) (hOrder : ordered.2 ≤ P ∧ usage ordered.1.2 ≤ U)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.2+(BinaryFourRestoredMeasured.afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤
      156*(P+BinaryFourOrderedMeasured.workEnvelope s K store.width store.cap.value+1700) := by
  have he := after_order_bound store input hC hAd ordered hOrdered K outer scalar pc hp
  have hw := (BinaryFourRestoredMeasured.afterOrder_bounds store input source hC hR hAd s hs hH ordered hOrdered P U hOrder K outer scalar pc hp).1
  simp only [BinaryFourRestoredMeasured.afterOrderWithDrawExtras_compat] at he ⊢
  omega

theorem restored_price (store : BinarySeedLookupTree.Store) (input : BinaryFourRestoredMeasured.Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).1.2+(BinaryFourRestoredMeasured.runWithDrawExtras store input hC hAd K outer scalar pc hp).2 ≤
      156*(BinaryFourRestoredMeasured.workEnvelope s K store.width store.cap.value) := by
  have he := restored_bound store input hC hAd K outer scalar pc hp
  have hw := (BinaryFourRestoredMeasured.run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp).1
  simp only [BinaryFourRestoredMeasured.runWithDrawExtras_compat] at he ⊢
  omega

theorem uniform_price {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp).2 ≤
      156*(BinaryWordGroupCompleteMeasured.uniformPrice n m s K store.width store.cap.value) := by
  have he := uniform_bound store input hC hAd hm routes K scalar pc hp
  have hw := (BinaryWordGroupCompleteMeasured.uniformRun_bounds store input hC hAd hm routes hRoutesC s hs hHeight hRoutes K scalar pc hp).1
  simp only [BinaryWordGroupCompleteMeasured.uniformRunWithDrawExtras_compat] at he ⊢
  omega

theorem mixed_two_price {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp).2 ≤
      156*(BinaryWordGroupCompleteMeasured.mixedTwoPrice n s K store.width store.cap.value) := by
  have he := mixed_two_bound store input hC hAd routes pivot K scalar pc hp
  have hw := (BinaryWordGroupCompleteMeasured.mixedTwoRun_bounds store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K scalar pc hp).1
  simp only [BinaryWordGroupCompleteMeasured.mixedTwoRunWithDrawExtras_compat] at he ⊢
  omega

theorem mixed_three_price {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupCompleteMeasured.mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp).1.2+(BinaryWordGroupCompleteMeasured.mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp).2 ≤
      156*(BinaryWordGroupCompleteMeasured.mixedThreePrice n s K store.width store.cap.value) := by
  have he := mixed_three_bound store input hC hAd routes pivot K outer scalar pc hp
  have hw := (BinaryWordGroupCompleteMeasured.mixedThreeRun_bounds store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K outer scalar pc hp).1
  simp only [BinaryWordGroupCompleteMeasured.mixedThreeRunWithDrawExtras_compat] at he ⊢
  omega

theorem draw_two_price {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : MixedHeights input s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤
      156*(BinaryWordGroupCompleteMeasured.mixedTwoPrice n s K store.width store.cap.value) := by
  have he := draw_two_bound store input hC hAd hTwo routes pivot K scalar pc hp
  have hw := (BinaryWordTerminalCompleteMeasured.drawTwo_bounds store input hC hAd hTwo routes pivot hRoutesC s hs hHeight hRoutes K scalar pc hp).1
  simp only [BinaryWordTerminalCompleteMeasured.drawTwoWithDrawExtras_compat] at he ⊢
  omega

theorem draw_three_price {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : MixedHeights input s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤
      156*(BinaryWordGroupCompleteMeasured.mixedThreePrice n s K store.width store.cap.value) := by
  have he := draw_three_bound store input hC hAd hThree routes pivot K outer scalar pc hp
  have hw := (BinaryWordTerminalCompleteMeasured.drawThree_bounds store input hC hAd hThree routes pivot hRoutesC s hs hHeight hRoutes K outer scalar pc hp).1
  simp only [BinaryWordTerminalCompleteMeasured.drawThreeWithDrawExtras_compat] at he ⊢
  omega

theorem terminal_price {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.runWithDrawExtras store prepared hC hAd K outer scalar pc hp).1.2+(BinaryWordTerminalCompleteMeasured.runWithDrawExtras store prepared hC hAd K outer scalar pc hp).2 ≤
      156*(BinaryWordTerminalCompleteMeasured.workEnvelope n s K store.width store.cap.value) := by
  have he := terminal_bound store prepared hC hAd K outer scalar pc hp
  have hw := (BinaryWordTerminalCompleteMeasured.run_bounds store prepared hC hAd s hs hUniform hMixed hRoutes K outer scalar pc hp).1
  simp only [BinaryWordTerminalCompleteMeasured.runWithDrawExtras_compat] at he ⊢
  omega

end Blotto.BinaryReturnedTerminalDrawExtras
