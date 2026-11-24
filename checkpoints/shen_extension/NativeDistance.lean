import checkpoints.shen_extension.WeightedJointCatalog

/-!
# The distance parameter behind "parent", "kin" and "two-step"

Every guard in the repair tests is one inequality. A walk of `d` arcs from `a` to `b` in a retained
graph on the survivors, together with a native route of `β` arcs from `b` back to `a` (through any
labels of `V`, erased ones included), closes a native walk, so `q < d + β` (`out_and_back`).

The catalog states this at `β = 1` (an arc), `β = 2` (a parent, a common parent, kin labels, a
two-step route). Here `β` is a free parameter.

* `pair_slack`: two new arcs can block each other only if the two native back-distances, from each
  tail to the other head, add up to at least `q + 4`.
* `cycle_slack`: around a blocking cycle of `n` labels the native back-distances add up to at least
  `n (q + 2) - q`.
* `near_iff`: if every tail has a native route of at most `β₀` arcs to every head and
  `2 β₀ < q + 4`, the family is safe exactly when each label passes its own test. `β₀ = 2` is the
  common-parent case.
* `ball_parent_row`, `ball_bypass`: the two obstruction laws with menus enlarged from the heads of
  the erased label to its forward ball of radius `g`, for every `g` with `2 (g + 1) < q + 4`;
  `g = (q+1)/2` always qualifies.
-/

namespace LeanCH.BR.NativeDistance
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay BypassTwoStepRow JointShortcut
  JointShortcutReplay LoneRow

variable {D K : CH.Digraph} {V U : Finset ℕ} {q : ℕ} {F : Finset Arc}

/-- **Out and back.** -/
theorem out_and_back (free : QFree D V q) (uv : U ⊆ V)
    (sub : ∀ a b, K a b = true → D a b = true) {a b d β : ℕ}
    (w : Walk K U a b d) (route : Walk D V b a β) (pos : 0 < β) : q < d + β := by
  by_contra short
  exact free a (d + β) (by omega) (by omega) (((walk_sub sub w).mono uv).append route)

/-- **Two labels.** Cross blocking forces the two native back-distances to add up to `q + 4`. -/
theorem pair_slack (free : QFree D V q) (uv : U ⊆ V)
    (sub : ∀ a b, K a b = true → D a b = true) {e₁ e₂ : Arc} {d₁ d₂ β₁ β₂ : ℕ}
    (w₁ : Walk K U e₁.2 e₂.1 d₁) (w₂ : Walk K U e₂.2 e₁.1 d₂) (cross : d₁ + d₂ + 2 ≤ q)
    (r₁ : Walk D V e₂.1 e₁.2 β₁) (r₂ : Walk D V e₁.1 e₂.2 β₂) (p₁ : 0 < β₁) (p₂ : 0 < β₂) :
    q + 4 ≤ β₁ + β₂ := by
  have := out_and_back free uv sub w₁ r₁ p₁
  have := out_and_back free uv sub w₂ r₂ p₂
  omega

/-- **Any number of labels.** For the cyclic list returned by the joint obstruction, native routes
from each next tail back to the current head have total length at least `n (q + 2) - q`. -/
theorem cycle_slack (free : QFree D V q) (uv : U ⊆ V)
    (sub : ∀ a b, K a b = true → D a b = true) {n : ℕ} {lab : ℕ → Arc} {len β : ℕ → ℕ}
    (steps : ∀ l < n, Walk K U (lab l).2 (lab (l + 1)).1 (len l))
    (routes : ∀ l < n, 0 < β l ∧ Walk D V (lab (l + 1)).1 (lab l).2 (β l))
    (budget : ∑ l ∈ range n, (len l + 1) ≤ q) :
    n * (q + 2) ≤ q + ∑ l ∈ range n, β l := by
  have each : ∀ l ∈ range n, q + 2 ≤ (len l + 1) + β l := fun l hl => by
    have hl' := mem_range.mp hl
    have := out_and_back free uv sub (steps l hl') (routes l hl').2 (routes l hl').1
    omega
  have total := sum_le_sum each
  rw [sum_const, card_range, smul_eq_mul, sum_add_distrib] at total
  exact total.trans (Nat.add_le_add_right budget _)

/-- **Near labels never block each other.** If every tail reaches every head natively within `β₀`
arcs and `2 β₀ < q + 4`, the family is safe exactly when no head returns to its own tail within
`q - 1` arcs. -/
theorem near_iff (free : QFree D V q) (uv : U ⊆ V)
    (sub : ∀ a b, K a b = true → D a b = true) (inU : ∀ j ∈ F, j.2 ∈ U) {β₀ : ℕ}
    (room : 2 * β₀ < q + 4)
    (near : ∀ j ∈ F, ∀ j' ∈ F, ∃ β, 0 < β ∧ β ≤ β₀ ∧ Walk D V j'.1 j.2 β) :
    QFree (install K F) U q ↔ ∀ j ∈ F, ∀ d, d + 1 ≤ q → ¬ Walk K U j.2 j.1 d := by
  constructor
  · intro safe j jF d cap w
    have closed : Walk (install K F) U j.2 j.2 (d + 1) :=
      (walk_sub (fun _ _ h => install_old h) w).snoc (inU j jF)
        (install_new (show (j.1, j.2) ∈ F from jF))
    exact safe j.2 (d + 1) (by omega) cap closed
  · intro own
    have old : QFree K U q := fun a l h1 h2 w => free a l h1 h2 ((walk_sub sub w).mono uv)
    have first : ∀ {i k : Arc} {c : ℕ}, Trail K U F i k c → i ∈ F → 0 < c → q + 2 ≤ c + β₀ := by
      intro i k c tr iF pos
      cases tr with
      | refl => omega
      | @step _ j _ d c' jF w rest =>
        obtain ⟨β, bpos, ble, route⟩ := near i iF j jF
        have := out_and_back free uv sub w route bpos
        omega
    refine (install_iff inU).mpr ⟨old, fun i iF c pos le tr => ?_⟩
    cases tr with
    | refl => omega
    | @step _ j _ d c' jF w rest =>
      obtain ⟨β, bpos, ble, route⟩ := near i iF j jF
      have long := out_and_back free uv sub w route bpos
      rcases Nat.eq_zero_or_pos c' with zero | cpos
      · have e := rest.eq_of_zero zero
        subst e
        exact own _ jF d (by omega) w
      · have := first rest jF cpos
        omega

/-- Within `g` native steps after `p`. -/
def after (D : CH.Digraph) (V : Finset ℕ) (p g z : ℕ) : Prop := ∃ i, 0 < i ∧ i ≤ g ∧ Walk D V p z i

theorem after_head {p z : ℕ} (zv : z ∈ V) (arc : D p z = true) {g : ℕ} (hg : 1 ≤ g) :
    after D V p g z := ⟨1, by decide, hg, .step zv arc (.refl z)⟩

theorem after_two {p h z : ℕ} (hv : h ∈ V) (zv : z ∈ V) (ph : D p h = true) (hz : D h z = true)
    {g : ℕ} (hg : 2 ≤ g) : after D V p g z := ⟨2, by decide, hg, .step hv ph (.step zv hz (.refl z))⟩

open Classical in
/-- Survivors within `g` native steps after `p` that the row `u` misses and that do not return to
`u` within `q-1` arcs of `K`. -/
noncomputable def clearBall (D K : CH.Digraph) (V U : Finset ℕ) (q g p u : ℕ) : Finset ℕ :=
  U.filter (fun z => after D V p g z ∧ D u z ≠ true ∧ ∀ d, d + 1 ≤ q → ¬ Walk K U z u d)

/-- **Common erased label, radius `g`.** Suppose every short row points to `p`. Then for every cut
inside the spare budgets some short row has fewer clear labels in the forward ball of radius `g`
around `p` than it is short. -/
theorem ball_parent_row {B : Finset ℕ} {t p g : ℕ} {C : ℕ → Finset ℕ} (free : QFree D V q)
    (none : NoHost q t) (bank : Eligible V B q t) (pv : p ∈ V) (room : 2 * (g + 1) < q + 4)
    (common : ∀ u ∈ V \ B, (outN D (V \ B) u).card < t → D u p = true)
    (budget : ∀ c ∈ V \ B, (C c).card ≤ spare D (V \ B) t c) :
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      (clearBall D (cut D C) V (V \ B) q g p u).card + (outN D (V \ B) u).card < t := by
  classical
  by_contra bad
  push Not at bad
  let P := (V \ B).filter (fun u => (outN D (V \ B) u).card < t)
  let F : Finset Arc :=
    (P ×ˢ (V \ B)).filter (fun j => j.2 ∈ clearBall D (cut D C) V (V \ B) q g p j.1)
  have memF : ∀ j, j ∈ F ↔ (j.1 ∈ V \ B ∧ (outN D (V \ B) j.1).card < t) ∧ j.2 ∈ V \ B ∧
      j.2 ∈ clearBall D (cut D C) V (V \ B) q g p j.1 := by
    intro j
    simp only [F, P, mem_filter, mem_product, and_assoc]
  have inU : ∀ j ∈ F, j.2 ∈ V \ B := fun j jF => ((memF j).mp jF).2.1
  have props : ∀ j ∈ F, after D V p g j.2 ∧ D j.1 j.2 ≠ true ∧
      ∀ d, d + 1 ≤ q → ¬ Walk (cut D C) (V \ B) j.2 j.1 d :=
    fun j jF => (mem_filter.mp ((memF j).mp jF).2.2).2
  have safe : QFree (install (cut D C) F) (V \ B) q := by
    refine (near_iff free sdiff_subset cut_sub inU room ?_).mpr (fun j jF => (props j jF).2.2)
    intro j jF j' jF'
    obtain ⟨i, ipos, ile, route⟩ := (props j jF).1
    obtain ⟨⟨ju, short⟩, _⟩ := (memF j').mp jF'
    exact ⟨i + 1, by omega, by omega, .step pv (common _ ju short) route⟩
  refine bank_exit none bank inU (fun j jF => (props j jF).2.1) (pays_of_spare budget ?_) safe
  intro u uu low
  have enough := bad u uu low
  have sub : clearBall D (cut D C) V (V \ B) q g p u ⊆ newHeads F u := by
    intro z hz
    exact mem_newHeads.mpr ((memF (u, z)).mpr ⟨⟨uu, low⟩, (mem_filter.mp hz).1, hz⟩)
  have := card_le_card sub
  omega

/-- **Bypass law, radius `g`.** Remove every arc into `x`. Each tight parent may take any survivor
within `g` native steps after `x` that it misses, erased intermediaries allowed. So for every
further affordable cut some tight parent is returned to, within `q-1` arcs, by every such label. -/
theorem ball_bypass {t x : ℕ} (L : Lone D V U q t x) (hq : 1 ≤ q) {g : ℕ}
    (room : 2 * (g + 1) < q + 4) {k : ℕ} (kc : k ∈ cols D U x) (C : ℕ → Finset ℕ)
    (budget : ∀ c ∈ U, (C c).card ≤ spare D (U.erase x) t c) :
    ∃ y, TightParent D U t x y ∧ ∀ a ∈ U, after D V x g a → D y a ≠ true →
      ∃ d, d + 1 ≤ q ∧ Walk (cut D (fun c => insert x (C c))) U a y d := by
  classical
  by_contra no
  push Not at no
  choose! f hf using no
  let FT : Finset Arc := (U.filter (fun y => TightParent D U t x y)).image (fun y => (y, f y))
  have memFT : ∀ j, j ∈ FT → TightParent D U t x j.1 ∧ j.2 = f j.1 := by
    intro j hj
    obtain ⟨y, yT, rfl⟩ := mem_image.mp hj
    exact ⟨(mem_filter.mp yT).2, rfl⟩
  have xv := L.uv L.xu
  have noloop : D x x ≠ true := loopfree L.free hq xv
  have notx : ∀ y, TightParent D U t x y → f y ≠ x := by
    intro y ty e
    obtain ⟨i, ipos, ile, route⟩ := (hf y ty).2.1
    rw [e] at route
    exact L.free x i ipos (by omega) route
  obtain ⟨ku, kx, xk⟩ := mem_cols.mp kc
  have base : QFree (install (cut D (fun c => insert x (C c))) FT) U q := by
    refine (near_iff L.free L.uv cut_sub ?_ room ?_).mpr ?_
    · intro j hj
      obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).1
    · intro j hj j' hj'
      obtain ⟨tight, e⟩ := memFT j hj
      obtain ⟨i, ipos, ile, route⟩ := (hf _ tight).2.1
      rw [e]
      exact ⟨i + 1, by omega, by omega, .step xv (memFT j' hj').1.2.2.1 route⟩
    · intro j hj
      obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).2.2.2
  have noin : ∀ c, install (cut D (fun c => insert x (C c))) FT c x ≠ true := by
    intro c h
    rcases install_cases h with old | new
    · simp [cut] at old
    · obtain ⟨tight, e⟩ := memFT _ new
      have e' : x = f c := e
      exact notx c tight e'.symm
  have safe := source_add base noin kx
  have inU : ∀ j ∈ insert (x, k) FT, j.2 ∈ U := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact ku
    · obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).1
  have fresh : ∀ j ∈ insert (x, k) FT, D j.1 j.2 ≠ true := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact xk
    · obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).2.2.1
  have pays : ∀ u ∈ U, t + (outN D U u ∩ insert x (C u)).card ≤
      (outN D U u).card + (newHeads (insert (x, k) FT) u).card := by
    intro u uu
    have b : (C u).card ≤ (outN D (U.erase x) u).card - t := budget u uu
    have er : outN D (U.erase x) u = (outN D U u).erase x := by
      ext j
      simp only [mem_outN, mem_erase]
      tauto
    rw [er] at b
    by_cases ux : D u x = true
    · have ne : u ≠ x := by
        rintro rfl
        exact noloop ux
      have one := card_erase_add_one (mem_outN.mpr ⟨L.xu, ux⟩)
      have ge := L.other u uu ne
      have capI : (outN D U u ∩ insert x (C u)).card ≤ (C u).card + 1 :=
        (card_le_card inter_subset_right).trans (card_insert_le _ _)
      by_cases tight : (outN D U u).card = t
      · have new : 0 < (newHeads (insert (x, k) FT) u).card :=
          card_pos.mpr ⟨f u, mem_newHeads.mpr (mem_insert_of_mem
            (mem_image.mpr ⟨u, mem_filter.mpr ⟨uu, uu, ne, ux, tight⟩, rfl⟩))⟩
        omega
      · omega
    · have capI : (outN D U u ∩ insert x (C u)).card ≤ (C u).card := by
        apply card_le_card
        intro j hj
        obtain ⟨jr, jc⟩ := mem_inter.mp hj
        rcases mem_insert.mp jc with e | e
        · exact absurd (e ▸ (mem_outN.mp jr).2) ux
        · exact e
      rw [erase_eq_of_notMem (fun hit => ux (mem_outN.mp hit).2)] at b
      by_cases e : u = x
      · have row := L.row
        have new : 0 < (newHeads (insert (x, k) FT) u).card :=
          card_pos.mpr ⟨k, mem_newHeads.mpr (by rw [e]; exact mem_insert_self _ _)⟩
        rw [e] at b capI ⊢
        rw [e] at new
        omega
      · have ge := L.other u uu e
        omega
  obtain ⟨E, free, deg⟩ := joint_host inU fresh pays safe
  exact L.none E U ⟨x, L.xu⟩ L.small free deg

/-! ### Packets and typed rules at the half radius `(q+1)/2` -/

theorem half_room (q : ℕ) : 2 * ((q + 1) / 2 + 1) < q + 4 := by omega

/-- The radius-`g` own-return debt at a shared erased label, for every affordable cut. -/
structure BallDebt (D : CH.Digraph) (V B : Finset ℕ) (q t p g : ℕ) : Prop where
  at_cut : ∀ C : ℕ → Finset ℕ, (∀ c ∈ V \ B, (C c).card ≤ spare D (V \ B) t c) →
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      (clearBall D (cut D C) V (V \ B) q g p u).card + (outN D (V \ B) u).card < t

@[aesop safe forward (immediate := [free,none,bank,pv,shared]) (rule_sets := [CHGraphFamilies])]
theorem shared_ball_debt {B : Finset ℕ} {t p : ℕ} (free : QFree D V q) (none : NoHost q t)
    (bank : Eligible V B q t) (pv : p ∈ V) (shared : SharedParent D (V \ B) t p) :
    BallDebt D V B q t p ((q + 1) / 2) :=
  ⟨fun _ budget => ball_parent_row free none bank pv (half_room q) shared.all_short budget⟩

@[aesop safe forward (immediate := [none,cell,shared]) (rule_sets := [CHGraphFamilies])]
theorem marked_ball_debt {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (none : NoHost q (r-1)) (cell : Marked X m)
    (shared : SharedParent X.D (X.V \ m.bank) (r-1) m.parent) :
    BallDebt X.D X.V m.bank q (r-1) m.parent ((q + 1) / 2) :=
  shared_ball_debt X.free none (marked_bank cell) (cell.sub cell.erased) shared

/-- The radius-`g` bypass law, for every affordable cut. -/
structure BallReturn (D : CH.Digraph) (V U : Finset ℕ) (q t x g : ℕ) : Prop where
  at_cut : ∀ C : ℕ → Finset ℕ, (∀ c ∈ U, (C c).card ≤ spare D (U.erase x) t c) →
    ∃ y, TightParent D U t x y ∧ ∀ a ∈ U, after D V x g a → D y a ≠ true →
      ∃ d, d + 1 ≤ q ∧ Walk (cut D (fun c => insert x (C c))) U a y d

@[aesop safe forward (immediate := [hq,none,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem marked_ball_bypass {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) :
    BallReturn X.D X.V (X.V \ m.bank) q (r-1) m.x ((q + 1) / 2) :=
  ⟨fun C budget => ball_bypass (on_cell none cell lone) (by omega) (half_room q)
    (LoneRowCatalog.target_column hq cell) C budget⟩

#print axioms out_and_back
#print axioms pair_slack
#print axioms cycle_slack
#print axioms near_iff
#print axioms ball_parent_row
#print axioms ball_bypass
#print axioms shared_ball_debt
#print axioms marked_ball_debt
#print axioms marked_ball_bypass
end LeanCH.BR.NativeDistance
