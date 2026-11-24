import checkpoints.pair_tilt_20261119.DeadExitInterval

/-! # Two dead exits on one inner ball, same native prices

`TwoExits` records exactly when these lemmas apply:

- one inner ball `R`, heads `H ⊆ R`, a root `a ∉ R` with `N⁺(a) = H`;
- flat native rows `c > w(V)`;
- two distinct exits `z₁, z₂ ∈ V ∖ R`, each dead on `R ∪ {itself}`.

Nothing here says that two such exits exist.

Notation: `q₁ = q−1`, `σ = c − w(V)`, `L r` is the native leakage of `r` outside `R`,
`M r` the residual leakage outside `R ∪ {z₁,z₂}`, `Q = q(σ + w(V∖R)) − c`, `G = q·w(H) − w(R)`,
and `Δ = w(N⁺[z₁] ∩ N⁺[z₂])`.

None of `Q`, `L`, `G` depends on the exit, so the four tests of `DeadExit.native_obstruction` are the
same inequalities at both exits. Only the incidence bits `(r→z₁, r→z₂)` decide which test applies.
Hence a row or pair that blocks one exit blocks the other whenever its bits allow
(`ah_implies_b0`).

The theorems below give the residual leakage a shared blocker needs, by incidence type. Rows of
type (0,0), (1,0) and (0,1) can never block with zero residual leakage. The types that use both
entries need overlap `Δ` between the exits' closed out-neighbourhoods. The missing graph premise
is `Disjoint N⁺[z₁] N⁺[z₂]`. -/
namespace LeanCH.BR.Closure.TwoExit
open Finset BRq2 BRq3 BR45 WeightedSD

def leak (E : CH.Digraph) (V R : Finset ℕ) (w : ℕ→ℚ) (i : ℕ) : ℚ :=
  mass ((V\R).filter (fun v => E i v=true)) w

def residual (E : CH.Digraph) (V R : Finset ℕ) (w : ℕ→ℚ) (z₁ z₂ i : ℕ) : ℚ :=
  mass ((((V\R).erase z₁).erase z₂).filter (fun v => E i v=true)) w

/-- The hypotheses under which the two-exit comparison is made. -/
structure TwoExits (q : ℕ) (E : CH.Digraph) (V R H : Finset ℕ) (w : ℕ→ℚ) (c : ℚ)
    (a z₁ z₂ : ℕ) : Prop where
  pos : ∀v∈V,0<w v
  flat : ∀i∈V,WeightedSD.row q E V w i=c
  high : mass V w<c
  rs : R⊆V
  hs : H⊆R
  av : a∈V
  aR : a∉R
  heads : ∀v∈V,E a v=true ↔ v∈H
  z₁v : z₁∈V
  z₂v : z₂∈V
  z₁R : z₁∉R
  z₂R : z₂∉R
  ne : z₁≠z₂
  a₁ : a≠z₁
  a₂ : a≠z₂
  dead₁ : ∀v∈insert z₁ R,E z₁ v=false
  dead₂ : ∀v∈insert z₂ R,E z₂ v=false

/-- Leakage splits into the two exits and the residual. -/
theorem leak_split {E : CH.Digraph} {V R : Finset ℕ} {w : ℕ→ℚ} {z₁ z₂ : ℕ} (ne : z₁≠z₂)
    (h₁ : z₁∈V\R) (h₂ : z₂∈V\R) (i : ℕ) :
    leak E V R w i=(if E i z₁=true then w z₁ else 0)+(if E i z₂=true then w z₂ else 0)+
      residual E V R w z₁ z₂ i := by
  have h₂' : z₂∈(V\R).erase z₁ := mem_erase.mpr ⟨ne.symm,h₂⟩
  unfold leak residual mass
  rw [sum_filter,sum_filter,← sum_erase_add _ _ h₁,← sum_erase_add _ _ h₂']
  ring

theorem residual_nonneg {E : CH.Digraph} {V R : Finset ℕ} {w : ℕ→ℚ} {z₁ z₂ : ℕ}
    (pos : ∀v∈V,0<w v) (i : ℕ) : 0≤residual E V R w z₁ z₂ i :=
  mass_nonneg (fun v hv =>
    (pos v (mem_sdiff.mp (mem_of_mem_erase (mem_of_mem_erase (mem_filter.mp hv).1))).1).le)

/-- A dead exit and its out-neighbourhood lie outside the inner ball and carry
`(c + q₁·w z)/q`. -/
theorem closed_out {q : ℕ} {E : CH.Digraph} {V R : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {z : ℕ}
    (flat : ∀i∈V,WeightedSD.row q E V w i=c) (zv : z∈V) (zr : z∉R)
    (dead : ∀v∈insert z R,E z v=false) :
    insert z (outN E V z)⊆V\R ∧ q*mass (insert z (outN E V z)) w=c+((q:ℚ)-1)*w z := by
  have zn : z∉outN E V z := fun h =>
    Bool.noConfusion ((dead z (mem_insert_self _ _)).symm.trans (mem_outN.mp h).2)
  refine ⟨?_,?_⟩
  · intro v hv
    rcases mem_insert.mp hv with e|hv
    · rw [e]; exact mem_sdiff.mpr ⟨zv,zr⟩
    · obtain ⟨vv,arc⟩ := mem_outN.mp hv
      exact mem_sdiff.mpr ⟨vv,fun vr =>
        Bool.noConfusion ((dead v (mem_insert_of_mem vr)).symm.trans arc)⟩
  · have row := flat z zv
    rw [WeightedSD.row,outW_eq_mass] at row
    have ins : mass (insert z (outN E V z)) w=w z+mass (outN E V z) w := by
      unfold mass; rw [sum_insert zn]
    rw [ins]
    linear_combination row

/-- One dead exit: `c + q₁·w z ≤ q·w(V∖R)`. -/
theorem bank_one {q : ℕ} {E : CH.Digraph} {V R : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {z : ℕ}
    (pos : ∀v∈V,0<w v) (flat : ∀i∈V,WeightedSD.row q E V w i=c) (zv : z∈V) (zr : z∉R)
    (dead : ∀v∈insert z R,E z v=false) :
    c+((q:ℚ)-1)*w z≤q*mass (V\R) w := by
  obtain ⟨sub,eq⟩ := closed_out flat zv zr dead
  have cap : mass (insert z (outN E V z)) w≤mass (V\R) w :=
    sum_le_sum_of_subset_of_nonneg sub (fun v hv _ => (pos v (mem_sdiff.mp hv).1).le)
  have := mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg q : (0:ℚ)≤q)
  linarith

/-- Two dead exits: `2c + q₁(w z₁ + w z₂) − qΔ ≤ q·w(V∖R)`. -/
theorem bank_two {q : ℕ} {E : CH.Digraph} {V R : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {z₁ z₂ : ℕ}
    (pos : ∀v∈V,0<w v) (flat : ∀i∈V,WeightedSD.row q E V w i=c)
    (z₁v : z₁∈V) (z₁R : z₁∉R) (dead₁ : ∀v∈insert z₁ R,E z₁ v=false)
    (z₂v : z₂∈V) (z₂R : z₂∉R) (dead₂ : ∀v∈insert z₂ R,E z₂ v=false) :
    2*c+((q:ℚ)-1)*(w z₁+w z₂)-q*mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w≤
      q*mass (V\R) w := by
  obtain ⟨s₁,e₁⟩ := closed_out flat z₁v z₁R dead₁
  obtain ⟨s₂,e₂⟩ := closed_out flat z₂v z₂R dead₂
  have ui : mass (insert z₁ (outN E V z₁)∪insert z₂ (outN E V z₂)) w+
      mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w=
      mass (insert z₁ (outN E V z₁)) w+mass (insert z₂ (outN E V z₂)) w := by
    unfold mass; exact sum_union_inter
  have cap : mass (insert z₁ (outN E V z₁)∪insert z₂ (outN E V z₂)) w≤mass (V\R) w :=
    sum_le_sum_of_subset_of_nonneg (union_subset s₁ s₂)
      (fun v hv _ => (pos v (mem_sdiff.mp hv).1).le)
  have := mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg q : (0:ℚ)≤q)
  have uq : (q:ℚ)*(mass (insert z₁ (outN E V z₁)∪insert z₂ (outN E V z₂)) w+
      mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w)=
      (q:ℚ)*(mass (insert z₁ (outN E V z₁)) w+mass (insert z₂ (outN E V z₂)) w) := by rw [ui]
  linarith

/-- The heads gap exceeds `σ + w z₁ + w z₂`: the root and both exits lie outside `R`. -/
theorem gap_bound {q : ℕ} {E : CH.Digraph} {V R H : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {a z₁ z₂ : ℕ}
    (X : TwoExits q E V R H w c a z₁ z₂) :
    (c-mass V w)+w z₁+w z₂≤q*mass H w-mass R w := by
  have hv : H⊆V := X.hs.trans X.rs
  have out : outN E V a=H := by
    ext v
    rw [mem_outN]
    exact ⟨fun ⟨vv,e⟩ => (X.heads v vv).mp e,fun vh => ⟨hv vh,(X.heads v (hv vh)).mpr vh⟩⟩
  have row := X.flat a X.av
  rw [WeightedSD.row,outW_eq_mass,out] at row
  have whole : mass V w=mass R w+mass (V\R) w := by
    unfold mass; rw [add_comm]; exact (sum_sdiff X.rs).symm
  have three : ({a,z₁,z₂} : Finset ℕ)⊆V\R := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact mem_sdiff.mpr ⟨X.av,X.aR⟩
    · exact mem_sdiff.mpr ⟨X.z₁v,X.z₁R⟩
    · exact mem_sdiff.mpr ⟨X.z₂v,X.z₂R⟩
  have cap := sum_le_sum_of_subset_of_nonneg three (fun v hv _ => (X.pos v (mem_sdiff.mp hv).1).le)
  have n1 : a∉({z₁,z₂} : Finset ℕ) := by simp [X.a₁,X.a₂]
  have n2 : z₁∉({z₂} : Finset ℕ) := by simp [X.ne]
  have m3 : (∑v∈({a,z₁,z₂} : Finset ℕ),w v)=w a+w z₁+w z₂ := by
    rw [sum_insert n1,sum_insert n2,sum_singleton]
    ring
  rw [m3] at cap
  change w a+w z₁+w z₂≤mass (V\R) w at cap
  linarith

/-- Natively `G > 0`, so a row failing the entering test (AH) also fails the missing test (B0)
at every exit it misses. -/
theorem ah_implies_b0 {q : ℕ} (hq : 2≤q) {G L Q : ℚ} (gp : 0<G)
    (ah : ((q:ℚ)-1)^2*G≤q*((q:ℚ)-1)*L-Q) : Q≤q*((q:ℚ)-1)*L := by
  have q1 : (0:ℚ)<(q:ℚ)-1 := by
    have : (2:ℚ)≤q := by exact_mod_cast hq
    linarith
  nlinarith [mul_pos (pow_pos q1 2) gp]

/-! ## Necessary residual leakage of a shared blocker, by incidence type -/

section Shared
variable {q : ℕ} {E : CH.Digraph} {V R H : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {a z₁ z₂ : ℕ}

private theorem split_bits (X : TwoExits q E V R H w c a z₁ z₂) (r : ℕ) :
    leak E V R w r=(if E r z₁=true then w z₁ else 0)+(if E r z₂=true then w z₂ else 0)+
      residual E V R w z₁ z₂ r :=
  leak_split X.ne (mem_sdiff.mpr ⟨X.z₁v,X.z₁R⟩) (mem_sdiff.mpr ⟨X.z₂v,X.z₂R⟩) r

/-- Type (0,0), missing both exits, failing B0: residual leakage at least
`(qσ + q₁·w zₖ)/(q q₁)` for each exit. -/
theorem miss_both (X : TwoExits q E V R H w c a z₁ z₂) {r : ℕ}
    (m₁ : E r z₁=false) (m₂ : E r z₂=false)
    (block : q*(c-mass V w+mass (V\R) w)-c≤q*((q:ℚ)-1)*leak E V R w r) :
    q*(c-mass V w)+((q:ℚ)-1)*w z₁≤q*((q:ℚ)-1)*residual E V R w z₁ z₂ r ∧
    q*(c-mass V w)+((q:ℚ)-1)*w z₂≤q*((q:ℚ)-1)*residual E V R w z₁ z₂ r := by
  have s := split_bits X r
  simp only [m₁,m₂,Bool.false_eq_true,ite_false,add_zero,zero_add] at s
  have b₁ := bank_one X.pos X.flat X.z₁v X.z₁R X.dead₁
  have b₂ := bank_one X.pos X.flat X.z₂v X.z₂R X.dead₂
  rw [s] at block
  constructor <;> linarith

/-- Type (1,0), entering only `z₁`, failing AH there (hence B0 at `z₂`): residual leakage at least
`((q + q₁²)σ + q₁²·w z₂)/(q q₁)`. The weight of the entered exit cancels. -/
theorem enter_first (X : TwoExits q E V R H w c a z₁ z₂) {r : ℕ}
    (e₁ : E r z₁=true) (m₂ : E r z₂=false)
    (block : ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
      q*((q:ℚ)-1)*leak E V R w r-(q*(c-mass V w+mass (V\R) w)-c)) :
    (q+((q:ℚ)-1)^2)*(c-mass V w)+((q:ℚ)-1)^2*w z₂≤q*((q:ℚ)-1)*residual E V R w z₁ z₂ r := by
  have s := split_bits X r
  simp only [e₁,m₂,ite_true,Bool.false_eq_true,ite_false,add_zero] at s
  have b₁ := bank_one X.pos X.flat X.z₁v X.z₁R X.dead₁
  have g := mul_le_mul_of_nonneg_left (gap_bound X) (sq_nonneg ((q:ℚ)-1))
  rw [s] at block
  nlinarith

/-- Type (1,1), entering both, failing AH: residual leakage at least
`((q + q₁²)σ + c − qΔ)/(q q₁)`. Both exit weights cancel. Each single bank gives
`(q + q₁²)σ ≤ q q₁ M + q₁·w zₖ`. -/
theorem enter_both (X : TwoExits q E V R H w c a z₁ z₂) {r : ℕ}
    (e₁ : E r z₁=true) (e₂ : E r z₂=true)
    (block : ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
      q*((q:ℚ)-1)*leak E V R w r-(q*(c-mass V w+mass (V\R) w)-c)) :
    (q+((q:ℚ)-1)^2)*(c-mass V w)+c-q*mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w≤
      q*((q:ℚ)-1)*residual E V R w z₁ z₂ r ∧
    (q+((q:ℚ)-1)^2)*(c-mass V w)≤q*((q:ℚ)-1)*residual E V R w z₁ z₂ r+((q:ℚ)-1)*w z₂ ∧
    (q+((q:ℚ)-1)^2)*(c-mass V w)≤q*((q:ℚ)-1)*residual E V R w z₁ z₂ r+((q:ℚ)-1)*w z₁ := by
  have s := split_bits X r
  simp only [e₁,e₂,ite_true] at s
  have b₁ := bank_one X.pos X.flat X.z₁v X.z₁R X.dead₁
  have b₂ := bank_one X.pos X.flat X.z₂v X.z₂R X.dead₂
  have b₁₂ := bank_two X.pos X.flat X.z₁v X.z₁R X.dead₁ X.z₂v X.z₂R X.dead₂
  have g := mul_le_mul_of_nonneg_left (gap_bound X) (sq_nonneg ((q:ℚ)-1))
  rw [s] at block
  refine ⟨by nlinarith,by nlinarith,by nlinarith⟩

/-- A pair in the same orientation at both exits: `a` enters both, `b` misses both.
Residual leakage `q₁(M a + q₁ M b) ≥ qσ + c − qΔ`, and `≥ qσ − q₁·w zₖ` from each single bank. -/
theorem pair_same (X : TwoExits q E V R H w c a z₁ z₂) {x y : ℕ}
    (x₁ : E x z₁=true) (x₂ : E x z₂=true) (y₁ : E y z₁=false) (y₂ : E y z₂=false)
    (block : q*(c-mass V w+mass (V\R) w)-c≤
      ((q:ℚ)-1)*(leak E V R w x+((q:ℚ)-1)*leak E V R w y)) :
    q*(c-mass V w)+c-q*mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w≤
      ((q:ℚ)-1)*(residual E V R w z₁ z₂ x+((q:ℚ)-1)*residual E V R w z₁ z₂ y) ∧
    q*(c-mass V w)≤((q:ℚ)-1)*(residual E V R w z₁ z₂ x+((q:ℚ)-1)*residual E V R w z₁ z₂ y)+
      ((q:ℚ)-1)*w z₂ ∧
    q*(c-mass V w)≤((q:ℚ)-1)*(residual E V R w z₁ z₂ x+((q:ℚ)-1)*residual E V R w z₁ z₂ y)+
      ((q:ℚ)-1)*w z₁ := by
  have sx := split_bits X x
  have sy := split_bits X y
  simp only [x₁,x₂,ite_true] at sx
  simp only [y₁,y₂,Bool.false_eq_true,ite_false,add_zero,zero_add] at sy
  have b₁ := bank_one X.pos X.flat X.z₁v X.z₁R X.dead₁
  have b₂ := bank_one X.pos X.flat X.z₂v X.z₂R X.dead₂
  have b₁₂ := bank_two X.pos X.flat X.z₁v X.z₁R X.dead₁ X.z₂v X.z₂R X.dead₂
  rw [sx,sy] at block
  refine ⟨by nlinarith,by nlinarith,by nlinarith⟩

/-- A pair in swapped orientation: `x` enters only `z₁`, `y` enters only `z₂`, and the pair
fails AB at `z₁` as `(x,y)` and at `z₂` as `(y,x)`. The weight of the exit entered by the
lighter-weighted member survives with coefficient `q₁(q−2)`. -/
theorem pair_swapped (X : TwoExits q E V R H w c a z₁ z₂) {x y : ℕ}
    (x₁ : E x z₁=true) (x₂ : E x z₂=false) (y₁ : E y z₁=false) (y₂ : E y z₂=true)
    (block₁ : q*(c-mass V w+mass (V\R) w)-c≤
      ((q:ℚ)-1)*(leak E V R w x+((q:ℚ)-1)*leak E V R w y))
    (block₂ : q*(c-mass V w+mass (V\R) w)-c≤
      ((q:ℚ)-1)*(leak E V R w y+((q:ℚ)-1)*leak E V R w x)) :
    q*(c-mass V w)+c-q*mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w≤
      ((q:ℚ)-1)*(residual E V R w z₁ z₂ x+((q:ℚ)-1)*residual E V R w z₁ z₂ y)+
        ((q:ℚ)-1)*((q:ℚ)-2)*w z₂ ∧
    q*(c-mass V w)+c-q*mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w≤
      ((q:ℚ)-1)*(residual E V R w z₁ z₂ y+((q:ℚ)-1)*residual E V R w z₁ z₂ x)+
        ((q:ℚ)-1)*((q:ℚ)-2)*w z₁ := by
  have sx := split_bits X x
  have sy := split_bits X y
  simp only [x₁,x₂,ite_true,Bool.false_eq_true,ite_false,add_zero] at sx
  simp only [y₁,y₂,ite_true,Bool.false_eq_true,ite_false,zero_add] at sy
  have b₁₂ := bank_two X.pos X.flat X.z₁v X.z₁R X.dead₁ X.z₂v X.z₂R X.dead₂
  rw [sx,sy] at block₁ block₂
  refine ⟨by nlinarith,by nlinarith⟩

end Shared

/-! ## Zero residual leakage -/

section Zero
variable {q : ℕ} {E : CH.Digraph} {V R H : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {a z₁ z₂ : ℕ}

/-- A shared single-row blocker with zero residual leakage must enter both exits, and the
exits must overlap: `qΔ ≥ (q + q₁²)σ + c` and `q₁·w zₖ ≥ (q + q₁²)σ`. Rows of type (0,0),
(1,0) and (0,1) are excluded outright. The missing test at `z₂` is listed for the statement's
symmetry; it follows from the others by `ah_implies_b0`. -/
theorem zero_residual_row (hq : 2≤q) (X : TwoExits q E V R H w c a z₁ z₂) {r : ℕ}
    (zero : residual E V R w z₁ z₂ r=0)
    (block₁ : E r z₁=false → q*(c-mass V w+mass (V\R) w)-c≤q*((q:ℚ)-1)*leak E V R w r)
    (enter₁ : E r z₁=true → ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
      q*((q:ℚ)-1)*leak E V R w r-(q*(c-mass V w+mass (V\R) w)-c))
    (_block₂ : E r z₂=false → q*(c-mass V w+mass (V\R) w)-c≤q*((q:ℚ)-1)*leak E V R w r)
    (enter₂ : E r z₂=true → ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
      q*((q:ℚ)-1)*leak E V R w r-(q*(c-mass V w+mass (V\R) w)-c)) :
    E r z₁=true ∧ E r z₂=true ∧
    (q+((q:ℚ)-1)^2)*(c-mass V w)+c≤q*mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w ∧
    (q+((q:ℚ)-1)^2)*(c-mass V w)≤((q:ℚ)-1)*w z₁ ∧
    (q+((q:ℚ)-1)^2)*(c-mass V w)≤((q:ℚ)-1)*w z₂ := by
  have σp : 0<c-mass V w := sub_pos.mpr X.high
  have q1 : (0:ℚ)<(q:ℚ)-1 := by
    have : (2:ℚ)≤q := by exact_mod_cast hq
    linarith
  have qq : (0:ℚ)<q+((q:ℚ)-1)^2 := by positivity
  have w₁ := X.pos z₁ X.z₁v
  have w₂ := X.pos z₂ X.z₂v
  have kill := mul_pos qq σp
  have qσ : 0≤(q:ℚ)*(c-mass V w) := mul_nonneg (Nat.cast_nonneg q) σp.le
  cases h₁ : E r z₁ <;> cases h₂ : E r z₂
  · obtain ⟨m,_⟩ := miss_both X h₁ h₂ (block₁ h₁)
    rw [zero] at m
    nlinarith [mul_pos q1 w₁]
  · have m := enter_first (z₁:=z₂) (z₂:=z₁)
      ⟨X.pos,X.flat,X.high,X.rs,X.hs,X.av,X.aR,X.heads,X.z₂v,X.z₁v,X.z₂R,X.z₁R,X.ne.symm,
        X.a₂,X.a₁,X.dead₂,X.dead₁⟩ h₂ h₁ (enter₂ h₂)
    have sym : residual E V R w z₂ z₁ r=residual E V R w z₁ z₂ r := by
      unfold residual; rw [erase_right_comm]
    rw [sym,zero] at m
    nlinarith [mul_pos (pow_pos q1 2) w₁]
  · have m := enter_first X h₁ h₂ (enter₁ h₁)
    rw [zero] at m
    nlinarith [mul_pos (pow_pos q1 2) w₂]
  · obtain ⟨m,m₂,m₁⟩ := enter_both X h₁ h₂ (enter₁ h₁)
    rw [zero] at m m₁ m₂
    refine ⟨rfl,rfl,by linarith,by linarith,by linarith⟩

/-- A same-orientation pair with zero residual leakage needs `qΔ ≥ qσ + c`. -/
theorem zero_residual_pair_same (X : TwoExits q E V R H w c a z₁ z₂) {x y : ℕ}
    (x₁ : E x z₁=true) (x₂ : E x z₂=true) (y₁ : E y z₁=false) (y₂ : E y z₂=false)
    (zx : residual E V R w z₁ z₂ x=0) (zy : residual E V R w z₁ z₂ y=0)
    (block : q*(c-mass V w+mass (V\R) w)-c≤
      ((q:ℚ)-1)*(leak E V R w x+((q:ℚ)-1)*leak E V R w y)) :
    q*(c-mass V w)+c≤q*mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w := by
  obtain ⟨m,_,_⟩ := pair_same X x₁ x₂ y₁ y₂ block
  rw [zx,zy] at m
  linarith

/-- At `q = 3`, a swapped pair with zero residual leakage needs overlap:
`2(3σ + c − 3Δ) ≤ 2(w z₁ + w z₂) < 2c`, so `3Δ > 3σ`. -/
theorem zero_residual_pair_swapped_three (X : TwoExits 3 E V R H w c a z₁ z₂) {x y : ℕ}
    (x₁ : E x z₁=true) (x₂ : E x z₂=false) (y₁ : E y z₁=false) (y₂ : E y z₂=true)
    (zx : residual E V R w z₁ z₂ x=0) (zy : residual E V R w z₁ z₂ y=0)
    (block₁ : (3:ℕ)*(c-mass V w+mass (V\R) w)-c≤
      (((3:ℕ):ℚ)-1)*(leak E V R w x+(((3:ℕ):ℚ)-1)*leak E V R w y))
    (block₂ : (3:ℕ)*(c-mass V w+mass (V\R) w)-c≤
      (((3:ℕ):ℚ)-1)*(leak E V R w y+(((3:ℕ):ℚ)-1)*leak E V R w x)) :
    c-mass V w<mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w := by
  obtain ⟨m₁,m₂⟩ := pair_swapped X x₁ x₂ y₁ y₂ block₁ block₂
  rw [zx,zy] at m₁ m₂
  have two : w z₁+w z₂≤mass V w := by
    have sub : ({z₁,z₂} : Finset ℕ)⊆V := by
      intro v hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact X.z₁v
      · exact X.z₂v
    have cap := sum_le_sum_of_subset_of_nonneg sub (fun v hv _ => (X.pos v hv).le)
    rw [sum_pair X.ne] at cap
    exact cap
  have hi := X.high
  push_cast at m₁ m₂
  linarith

/-- The missing graph premise: disjoint closed out-neighbourhoods of the two exits.
Under it no zero-residual shared row and no zero-residual same-orientation pair exists for any
`q ≥ 2`, and at `q = 3` no zero-residual swapped pair exists either. -/
theorem disjoint_overlap {E : CH.Digraph} {V : Finset ℕ} {w : ℕ→ℚ} {z₁ z₂ : ℕ}
    (P : Disjoint (insert z₁ (outN E V z₁)) (insert z₂ (outN E V z₂))) :
    mass (insert z₁ (outN E V z₁)∩insert z₂ (outN E V z₂)) w=0 := by
  rw [disjoint_iff_inter_eq_empty.mp P]
  simp [mass]

theorem disjoint_no_zero_row (hq : 2≤q) (X : TwoExits q E V R H w c a z₁ z₂)
    (P : Disjoint (insert z₁ (outN E V z₁)) (insert z₂ (outN E V z₂))) {r : ℕ}
    (zero : residual E V R w z₁ z₂ r=0)
    (block₁ : E r z₁=false → q*(c-mass V w+mass (V\R) w)-c≤q*((q:ℚ)-1)*leak E V R w r)
    (enter₁ : E r z₁=true → ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
      q*((q:ℚ)-1)*leak E V R w r-(q*(c-mass V w+mass (V\R) w)-c))
    (block₂ : E r z₂=false → q*(c-mass V w+mass (V\R) w)-c≤q*((q:ℚ)-1)*leak E V R w r)
    (enter₂ : E r z₂=true → ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
      q*((q:ℚ)-1)*leak E V R w r-(q*(c-mass V w+mass (V\R) w)-c)) : False := by
  obtain ⟨_,_,ovl,_,_⟩ := zero_residual_row hq X zero block₁ enter₁ block₂ enter₂
  rw [disjoint_overlap P] at ovl
  have σp : 0<c-mass V w := sub_pos.mpr X.high
  have m0 : 0≤mass V w := mass_nonneg (fun v hv => (X.pos v hv).le)
  have cp : 0<c := by linarith
  have qq : (0:ℚ)≤q+((q:ℚ)-1)^2 := by positivity
  nlinarith [mul_nonneg qq σp.le]

theorem disjoint_no_zero_pair (X : TwoExits q E V R H w c a z₁ z₂)
    (P : Disjoint (insert z₁ (outN E V z₁)) (insert z₂ (outN E V z₂))) {x y : ℕ}
    (x₁ : E x z₁=true) (x₂ : E x z₂=true) (y₁ : E y z₁=false) (y₂ : E y z₂=false)
    (zx : residual E V R w z₁ z₂ x=0) (zy : residual E V R w z₁ z₂ y=0)
    (block : q*(c-mass V w+mass (V\R) w)-c≤
      ((q:ℚ)-1)*(leak E V R w x+((q:ℚ)-1)*leak E V R w y)) : False := by
  have m := zero_residual_pair_same X x₁ x₂ y₁ y₂ zx zy block
  rw [disjoint_overlap P] at m
  have σp : 0<c-mass V w := sub_pos.mpr X.high
  have m0 : 0≤mass V w := mass_nonneg (fun v hv => (X.pos v hv).le)
  have cp : 0<c := by linarith
  nlinarith [mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) σp.le]

end Zero

/-! ## Both exits on a least source, with labels -/

/-- `native_obstruction` at both exits, with the heads alternative removed by the root.
The same `Q`, `L` and `G` appear in both lists; only the incidence bits differ. -/
theorem both_exits_labels {q : ℕ} {D E : CH.Digraph} {V R H : Finset ℕ} {w : ℕ→ℚ} {c : ℚ}
    {a z₁ z₂ : ℕ} (hq : 2≤q) (X : TwoExits q E V R H w c a z₁ z₂)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (sub : ∀i j,E i j=true → D i j=true)
    (live : H.Nonempty)
    (in₁ : insert z₁ R⊆V) (room₁ : (insert z₁ R).card+1<V.card)
    (ball₁ : BRsub.ballSet E (insert z₁ R) H (q-2)=R)
    (in₂ : insert z₂ R⊆V) (room₂ : (insert z₂ R).card+1<V.card)
    (ball₂ : BRsub.ballSet E (insert z₂ R) H (q-2)=R) :
    ∀ z ∈ ({z₁,z₂} : Finset ℕ),
      (∃b∈R,E b z=false ∧ q*(c-mass V w+mass (V\R) w)-c≤q*((q:ℚ)-1)*leak E V R w b) ∨
      (∃x∈R,E x z=true ∧ ∃y∈R,E y z=false ∧ q*(c-mass V w+mass (V\R) w)-c≤
        ((q:ℚ)-1)*(leak E V R w x+((q:ℚ)-1)*leak E V R w y)) ∨
      ∃x∈R,E x z=true ∧ ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
        q*((q:ℚ)-1)*leak E V R w x-(q*(c-mass V w+mass (V\R) w)-c) := by
  intro z hz
  have heads := DeadExit.native_heads_pass X.pos X.flat X.high X.av (X.hs.trans X.rs) X.heads X.rs X.aR
  have pick : ∀ zz, zz∉R → (∀v∈insert zz R,E zz v=false) → insert zz R⊆V →
      (insert zz R).card+1<V.card → BRsub.ballSet E (insert zz R) H (q-2)=R →
      (∃b∈R,E b zz=false ∧ q*(c-mass V w+mass (V\R) w)-c≤q*((q:ℚ)-1)*leak E V R w b) ∨
      (∃x∈R,E x zz=true ∧ ∃y∈R,E y zz=false ∧ q*(c-mass V w+mass (V\R) w)-c≤
        ((q:ℚ)-1)*(leak E V R w x+((q:ℚ)-1)*leak E V R w y)) ∨
      ∃x∈R,E x zz=true ∧ ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤
        q*((q:ℚ)-1)*leak E V R w x-(q*(c-mass V w+mass (V\R) w)-c) := by
    intro zz zr dead inside room ball
    rcases DeadExit.native_obstruction hq free small sub inside room X.hs live zr dead ball w
      X.pos X.flat with h|h
    · exact absurd heads (not_lt.mpr h)
    · exact h
  simp only [mem_insert,mem_singleton] at hz
  rcases hz with rfl|rfl
  · exact pick _ X.z₁R X.dead₁ in₁ room₁ ball₁
  · exact pick _ X.z₂R X.dead₂ in₂ room₂ ball₂

#print axioms leak_split
#print axioms bank_two
#print axioms gap_bound
#print axioms miss_both
#print axioms enter_first
#print axioms enter_both
#print axioms pair_same
#print axioms pair_swapped
#print axioms zero_residual_row
#print axioms zero_residual_pair_same
#print axioms zero_residual_pair_swapped_three
#print axioms disjoint_no_zero_row
#print axioms disjoint_no_zero_pair
#print axioms both_exits_labels
end LeanCH.BR.Closure.TwoExit
