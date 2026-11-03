import Blotto.GeneralPaperCachedMassJoin

/-! Sparse dyadic interval nodes with exact offsets and stored masses.
Uniform intervals are represented without enumerating their codes. Parent
rebuild uses current children and the actual shared power/rounded arithmetic
implementation. Whole-interval offset changes retain the cached base mass.
Contiguous-range traversal and its address/node ledger are not asserted here.
-/
namespace Blotto.GeneralPaperIntervalCache
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperCachedMassJoin
set_option autoImplicit false
set_option maxHeartbeats 2500000

inductive Node : ℕ → Type where
  | uniform (height offset : ℕ) : Node height
  | branch {height : ℕ} (offset : ℕ) (cached : Number) (left right : Node height) : Node (height+1)

def offset {height : ℕ} : Node height → ℕ
  | .uniform _ level => level
  | .branch level _ _ _ => level

def mass (prepared : Prepared) {height : ℕ} : Node height → Number
  | .uniform h _ => GeneralPaperDyadicShift.uniformMass prepared.format.unit prepared.format.fractionalBits h
  | .branch _ cached _ _ => cached

def exactMass (base : ℚ) {height : ℕ} : Node height → ℚ
  | .uniform h _ => (2:ℚ)^h
  | .branch _ _ left right => base^offset left*exactMass base left+base^offset right*exactMass base right

def CacheCorrect (lambda k : ℕ) {height : ℕ} (node : Node height) : Prop :=
  Normal (prepare lambda k).format.unit (mass (prepare lambda k) node) ∧
    0<(mass (prepare lambda k) node).mantissa ∧
    retention (prepare lambda k).format.unit^((GeneralPaperPowerPrecision.levelBound lambda k+2)*height)*
        exactMass (base k) node≤value (mass (prepare lambda k) node) ∧
      value (mass (prepare lambda k) node)≤exactMass (base k) node

def Valid (lambda k : ℕ) : {height : ℕ} → Node height → Prop
  | _,.uniform _ level => level≤GeneralPaperPowerPrecision.levelBound lambda k
  | _,node@(.branch level _ left right) => level≤GeneralPaperPowerPrecision.levelBound lambda k ∧
      Valid lambda k left ∧ Valid lambda k right ∧ CacheCorrect lambda k node

def raiseRoot {height : ℕ} (amount : ℕ) : Node height → Node height
  | .uniform h level => .uniform h (level+amount)
  | .branch level cached left right => .branch (level+amount) cached left right

def rebuild (prepared : Prepared) {height : ℕ} (level : ℕ) (left right : Node height) : Node (height+1) :=
  .branch level (recompute prepared (offset left) (mass prepared left) (offset right) (mass prepared right)).number left right

def expand (prepared : Prepared) (height level : ℕ) : Node (height+1) :=
  .branch level (GeneralPaperDyadicShift.uniformMass prepared.format.unit prepared.format.fractionalBits (height+1))
    (.uniform height 0) (.uniform height 0)

def nodes {height : ℕ} : Node height → ℕ
  | .uniform _ _ => 1
  | .branch _ _ left right => 1+nodes left+nodes right

theorem uniform_correct (lambda k height level : ℕ) : CacheCorrect lambda k (.uniform height level) := by
  have hu := prepared_unit_positive lambda k
  have hr := retention_bounds (prepare lambda k).format.unit (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hp : retention (prepare lambda k).format.unit^((GeneralPaperPowerPrecision.levelBound lambda k+2)*height)≤1 :=
    pow_le_one₀ hr.1.le hr.2
  unfold CacheCorrect
  dsimp only [mass,exactMass]
  rw [GeneralPaperDyadicShift.uniform_value (prepare lambda k).format.unit
    (prepare lambda k).format.fractionalBits height (GeneralPaperPowerPrecision.unit_power lambda k)]
  exact ⟨GeneralPaperDyadicShift.uniform_normal _ _ height hu,
    GeneralPaperDyadicShift.uniform_positive _ _ height hu,
    mul_le_of_le_one_left (by positivity) hp,le_refl _⟩

theorem valid_cache (lambda k : ℕ) {height : ℕ} (node : Node height) (h : Valid lambda k node) : CacheCorrect lambda k node := by
  cases node with
  | uniform height level => exact uniform_correct lambda k height level
  | branch level cached left right => exact h.2.2.2

theorem valid_offset (lambda k : ℕ) {height : ℕ} (node : Node height) (h : Valid lambda k node) :
    offset node≤GeneralPaperPowerPrecision.levelBound lambda k := by
  cases node with
  | uniform height level => exact h
  | branch level cached left right => exact h.1

theorem exact_mass_positive (b : ℚ) (hb : 0<b) {height : ℕ} (node : Node height) : 0<exactMass b node := by
  induction node with
  | uniform height level => dsimp [exactMass]; positivity
  | branch level cached left right ihl ihr =>
    dsimp only [exactMass]
    exact add_pos (mul_pos (pow_pos hb _) ihl) (mul_pos (pow_pos hb _) ihr)

theorem rebuild_valid (lambda k : ℕ) {height : ℕ} (level : ℕ) (left right : Node height)
    (hLevel : level≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hl : Valid lambda k left) (hr : Valid lambda k right) :
    Valid lambda k (rebuild (prepare lambda k) level left right) := by
  have hlc := valid_cache lambda k left hl
  have hrc := valid_cache lambda k right hr
  have hlo := valid_offset lambda k left hl
  have hro := valid_offset lambda k right hr
  have hBounds := recompute_bounds lambda k height (offset left) (offset right)
    (mass (prepare lambda k) left) (mass (prepare lambda k) right)
    (exactMass (base k) left) (exactMass (base k) right) hlo hro hlc.1 hrc.1
    (exact_mass_positive (base k) (base_positive k) left).le
    (exact_mass_positive (base k) (base_positive k) right).le hlc.2.2.1 hrc.2.2.1 hlc.2.2.2 hrc.2.2.2
  refine ⟨hLevel,hl,hr,?_,?_,hBounds.1,hBounds.2⟩
  · exact recompute_normal lambda k _ _ _ _ hlo hro hlc.1 hrc.1
  · exact recompute_positive lambda k _ _ _ _ hlo hro hlc.1 hrc.1 hlc.2.1

theorem raised_mass {height : ℕ} (prepared : Prepared) (amount : ℕ) (node : Node height) :
    mass prepared (raiseRoot amount node)=mass prepared node := by cases node <;> rfl

theorem raised_exact_mass {height : ℕ} (b : ℚ) (amount : ℕ) (node : Node height) :
    exactMass b (raiseRoot amount node)=exactMass b node := by cases node <;> rfl

theorem raised_valid (lambda k : ℕ) {height : ℕ} (amount : ℕ) (node : Node height)
    (h : Valid lambda k node) (hLevel : offset node+amount≤GeneralPaperPowerPrecision.levelBound lambda k) :
    Valid lambda k (raiseRoot amount node) := by
  cases node with
  | uniform height level => exact hLevel
  | branch level cached left right => exact ⟨hLevel,h.2.1,h.2.2.1,h.2.2.2⟩

theorem expanded_exact_mass (prepared : Prepared) (b : ℚ) (height level : ℕ) :
    exactMass b (expand prepared height level)=exactMass b (.uniform (height+1) level) := by
  simp only [expand,exactMass,offset,pow_zero,one_mul,pow_succ]
  ring

theorem expanded_valid (lambda k height level : ℕ) (hLevel : level≤GeneralPaperPowerPrecision.levelBound lambda k) :
    Valid lambda k (expand (prepare lambda k) height level) := by
  have hCache := uniform_correct lambda k (height+1) level
  have hExact := expanded_exact_mass (prepare lambda k) (base k) height level
  have hMass : mass (prepare lambda k) (expand (prepare lambda k) height level)=
      mass (prepare lambda k) (.uniform (height+1) level) := rfl
  have hNew : CacheCorrect lambda k (expand (prepare lambda k) height level) := by
    unfold CacheCorrect at hCache ⊢
    rw [hMass,hExact]
    exact hCache
  exact ⟨hLevel,Nat.zero_le _,Nat.zero_le _,hNew⟩

theorem raised_nodes {height : ℕ} (amount : ℕ) (node : Node height) : nodes (raiseRoot amount node)=nodes node := by
  cases node <;> rfl

theorem expanded_nodes (prepared : Prepared) (height level : ℕ) : nodes (expand prepared height level)=3 := rfl

end Blotto.GeneralPaperIntervalCache
