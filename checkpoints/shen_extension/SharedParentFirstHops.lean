import checkpoints.shen_extension.JointShortcutReplay

namespace LeanCH.BR.SharedParentFirstHops
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay JointShortcut JointShortcutReplay

open Classical in
/-- Distinct first arcs out of z charged by the proposed shortcuts u → z.
Several assigned rows, or several return walks, can charge the same arc only once. -/
noncomputable def bill (D : CH.Digraph) (U : Finset ℕ) (q : ℕ) (F : Finset Arc) (z : ℕ) :=
  (outN D U z).filter (fun b => ∃ u, (u,z) ∈ F ∧ Walk D U b u (q-2))

private theorem keep_suffix {D V U q p} {C : ℕ → Finset ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (pv : p ∈ V)
    (support : ∀ a, D p a ≠ true → C a = ∅)
    {a u k} (path : Walk D U a u k) (au : a ∈ U) (up : D u p = true)
    (short : k+2 ≤ q) : Walk (cut D C) U a u k := by
  induction path with
  | refl => exact .refl _
  | @step a b u k bu ab tail ih =>
    have off : D p a ≠ true := by
      intro pa
      exact free p (k+1+1+1) (by omega) (by omega)
        (.step (uv au) pa (((Walk.step (D:=D) bu ab tail).mono uv).snoc pv up))
    exact .step bu (by simp [cut,ab,support a off]) (ih bu up (by omega))

private theorem first_step {K U a u k} (path : Walk K U a u (k+1)) :
    ∃ b ∈ U, K a b = true ∧ Walk K U b u k := by
  cases path with
  | step bu edge rest => exact ⟨_,bu,edge,rest⟩

/-- For cuts at the heads of p, these very first arcs are individually necessary
and together sufficient. The other arcs of each suffix survive all such cuts. -/
theorem safe_iff_cuts_bills {D V U q p} {C : ℕ → Finset ℕ} {F : Finset Arc}
    (free : QFree D V q) (hq : 2 ≤ q) (uv : U ⊆ V) (pv : p ∈ V)
    (heads : ∀ j ∈ F, j.2 ∈ U ∧ D p j.2 = true) (tails : ∀ j ∈ F, D j.1 p = true)
    (support : ∀ a, D p a ≠ true → C a = ∅) :
    QFree (install (cut D C) F) U q ↔ ∀ z, bill D U q F z ⊆ C z := by
  classical
  have tests := kin_iff (F:=F) free (by omega) uv (cut_sub (C:=C))
    (fun j hj => (heads j hj).1) (fun _ => p) (fun _ => 0)
    (fun _ _ => pv) (fun j hj => (heads j hj).2) (fun _ _ j hj _ => tails j hj)
  rw [tests]
  constructor
  · intro no z b hb
    obtain ⟨edge,u,assigned,suffix⟩ := mem_filter.mp hb
    obtain ⟨bu,zb⟩ := mem_outN.mp edge
    by_contra kept
    have suffix' := keep_suffix free uv pv support suffix bu (tails (u,z) assigned) (by omega)
    apply no (u,z) assigned
    rw [show q-1 = q-2+1 by omega]
    exact .step bu (by simp [cut,zb,kept]) suffix'
  · intro covers j hj path
    rw [show q-1 = q-2+1 by omega] at path
    obtain ⟨b,bu,edge,rest⟩ := first_step path
    have both := Bool.and_eq_true_iff.mp edge
    have charged : b ∈ bill D U q F j.2 :=
      mem_filter.mpr ⟨mem_outN.mpr ⟨bu,both.1⟩, j.1,hj,walk_sub cut_sub rest⟩
    exact (of_decide_eq_true both.2) (covers _ charged)

theorem bill_supported {D U q F p} (heads : ∀ j ∈ F, D p (Prod.snd j) = true)
    (z : ℕ) (off : D p z ≠ true) : bill D U q F z = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨_,u,assigned,_⟩ := mem_filter.mp hb
  exact off (heads (u,z) assigned)

/-- On a fixed bank, any collection of proposed missing heads that fills every
shortage must overload a physical first-hop row, even when returns share arcs. -/
theorem overloaded {D V B q t p} {F : Finset Arc}
    (none : NoHost q t) (bank : Eligible V B q t) (free : QFree D V q)
    (hq : 2 ≤ q) (pv : p ∈ V)
    (heads : ∀ j ∈ F, j.2 ∈ V \ B ∧ D p j.2 = true) (tails : ∀ j ∈ F, D j.1 p = true)
    (fresh : ∀ j ∈ F, D j.1 j.2 ≠ true)
    (cover : ∀ u ∈ V \ B, (outN D (V \ B) u).card < t →
      t ≤ (outN D (V \ B) u).card + (newHeads F u).card) :
    ∃ z ∈ V \ B, (∃ u, (u,z) ∈ F) ∧ spare D (V \ B) t z < (bill D (V \ B) q F z).card := by
  classical
  let C := bill D (V \ B) q F
  have safe := (safe_iff_cuts_bills (C:=C) free hq sdiff_subset pv heads tails
    (bill_supported (fun j hj => (heads j hj).2))).mpr (fun _ => Subset.rfl)
  by_contra! avoid
  apply bank_exit none bank (fun j hj => (heads j hj).1) fresh _ safe
  apply pays_of_spare _ cover
  intro z zu
  by_cases assigned : ∃ u, (u,z) ∈ F
  · exact avoid z zu assigned
  · have empty : C z = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨_,u,uf,_⟩ := mem_filter.mp hb
      exact assigned ⟨u,uf⟩
    simp [empty]

private theorem keep_middle {D V U q p u} {C : ℕ → Finset ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (pv : p ∈ V) (us : u ∈ V) (up : D u p = true)
    (support : ∀ a b, b ∈ C a → D p a = true ∨ D b p = true)
    {a y k i} (middle : Walk D U a y k) (au : a ∈ U) (prefixWalk : Walk D V p a i)
    (yu : D y u = true) (remaining : k+3 ≤ q) (used : i+k+1 ≤ q) :
    Walk (cut D C) U a y k := by
  induction middle generalizing i with
  | refl => exact .refl _
  | @step a b y k bu ab rest ih =>
    have prefix' := prefixWalk.snoc (uv bu) ab
    have kept : b ∉ C a := by
      intro removed
      rcases support a b removed with pa | bp
      · exact free p (k+1+1+1+1) (by omega) (by omega)
          (.step (uv au) pa ((((Walk.step bu ab rest).mono uv).snoc us yu).snoc pv up))
      · exact free p (i+1+1) (by omega) (by omega) (prefix'.snoc pv bp)
    exact .step bu (by simp [cut,ab,kept]) (ih bu prefix' yu (by omega) (by omega))

/-- Cut an arc out of any head of p or into any parent of p. For every proposed
shortcut u → z, each native middle b ⇝ y gives a constraint on just two physical
arcs: cut z → b or cut y → u. The same cut is used for all constraints. -/
theorem safe_iff_covers_ends {D V U q p} {C : ℕ → Finset ℕ} {F : Finset Arc}
    (free : QFree D V q) (hq : 3 ≤ q) (uv : U ⊆ V) (pv : p ∈ V)
    (heads : ∀ j ∈ F, j.2 ∈ U ∧ D p j.2 = true)
    (tails : ∀ j ∈ F, j.1 ∈ U ∧ D j.1 p = true)
    (support : ∀ a b, b ∈ C a → D p a = true ∨ D b p = true) :
    QFree (install (cut D C) F) U q ↔
      ∀ j ∈ F, ∀ b ∈ U, ∀ y ∈ U, D j.2 b = true → Walk D U b y (q-3) →
        D y j.1 = true → b ∈ C j.2 ∨ j.1 ∈ C y := by
  classical
  rw [kin_iff (F:=F) free (by omega) uv (cut_sub (C:=C)) (fun j hj => (heads j hj).1)
    (fun _ => p) (fun _ => 0) (fun _ _ => pv) (fun j hj => (heads j hj).2)
    (fun _ _ j hj _ => (tails j hj).2)]
  have length : q-1 = q-3+1+1 := by omega
  constructor
  · intro clear j hj b bu y _ zb middle yu
    by_contra! both
    have prefixWalk : Walk D V p b 2 :=
      .step (uv (heads j hj).1) (heads j hj).2 (.step (uv bu) zb (.refl _))
    have inner := keep_middle free uv pv (uv (tails j hj).1) (tails j hj).2 support
      middle bu prefixWalk yu (by omega) (by omega)
    apply clear j hj
    rw [length]
    exact .step bu (by simp [cut,zb,both.1])
      (inner.snoc (tails j hj).1 (by simp [cut,yu,both.2]))
  · intro covered j hj path
    rw [length] at path
    obtain ⟨b,bu,first,rest⟩ := first_step path
    obtain ⟨y,middle,_,last⟩ := rest.unsnoc
    have ys := middle.end_mem_or.elim (fun eq => eq ▸ bu) id
    have left := Bool.and_eq_true_iff.mp first
    have right := Bool.and_eq_true_iff.mp last
    rcases covered j hj b bu y ys left.1 (walk_sub cut_sub middle) right.1 with hit | hit
    · exact (of_decide_eq_true left.2) hit
    · exact (of_decide_eq_true right.2) hit

/-- The two endpoint bills use actual outgoing-arc budgets in the same graph. -/
theorem paid_end_cover {D V B q t p} {C : ℕ → Finset ℕ} {F : Finset Arc}
    (none : NoHost q t) (bank : Eligible V B q t) (free : QFree D V q)
    (hq : 3 ≤ q) (pv : p ∈ V)
    (heads : ∀ j ∈ F, j.2 ∈ V \ B ∧ D p j.2 = true)
    (tails : ∀ j ∈ F, j.1 ∈ V \ B ∧ D j.1 p = true)
    (fresh : ∀ j ∈ F, D j.1 j.2 ≠ true)
    (budget : ∀ u ∈ V \ B, (C u).card ≤ spare D (V \ B) t u)
    (cover : ∀ u ∈ V \ B, (outN D (V \ B) u).card < t →
      t ≤ (outN D (V \ B) u).card + (newHeads F u).card)
    (support : ∀ a b, b ∈ C a → D p a = true ∨ D b p = true)
    (hits : ∀ j ∈ F, ∀ b ∈ V \ B, ∀ y ∈ V \ B, D j.2 b = true →
      Walk D (V \ B) b y (q-3) → D y j.1 = true → b ∈ C j.2 ∨ j.1 ∈ C y) : False :=
  bank_exit none bank (fun j hj => (heads j hj).1) fresh (pays_of_spare budget cover)
    ((safe_iff_covers_ends free hq sdiff_subset pv heads tails support).mpr hits)

/-- All physically available proposals through p on the deficient rows. -/
def offers (D : CH.Digraph) (U : Finset ℕ) (t p : ℕ) : Finset Arc :=
  ((U.filter (fun u => (outN D U u).card < t)) ×ˢ outN D U p).filter
    (fun j => D j.1 j.2 ≠ true)

open Classical in
/-- A head on an actual return to this u, with more distinct charged first
arcs than its row can cut. Count each such head once for this debtor. -/
noncomputable def crowded (D K : CH.Digraph) (U : Finset ℕ) (q t p u : ℕ) :=
  (outN D U p \ outN D U u).filter (fun z =>
    spare D U t z < (bill K U q (offers D U t p) z).card ∧ Walk K U z u (q-1))

/-- One physical cut can pay all affordable first-hop bills at once, after any
affordable cuts L away from p's heads. At the row forced by no-host, all but
strictly fewer than its shortage of the eligible heads are crowded. -/
theorem pressure {D U q t p} (debt : OwnReturnDebt D U q t p) (hq : 2 ≤ q)
    (L : ℕ → Finset ℕ) (budget : ∀ a ∈ U, (L a).card ≤ spare D U t a)
    (untouched : ∀ a, D p a = true → L a = ∅) :
    ∃ u ∈ U, (outN D U u).card < t ∧
      ((outN D U p \ outN D U u) \ crowded D (cut D L) U q t p u).card +
          (outN D U u).card < t := by
  classical
  let K := cut D L
  let cost := bill K U q (offers D U t p)
  let C := fun z => if D p z = true then
    (if (cost z).card ≤ spare D U t z then cost z else ∅) else L z
  have affordable : ∀ a ∈ U, (C a).card ≤ spare D U t a := by
    intro a au
    by_cases pa : D p a = true
    · by_cases fits : (cost a).card ≤ spare D U t a <;> simp [C,pa,fits]
    · simpa [C,pa] using budget a au
  have sub : ∀ a b, cut D C a b = true → K a b = true := by
    intro a b edge
    by_cases pa : D p a = true
    · simp [K,cut,untouched a pa,cut_sub _ _ edge]
    · simpa [K,cut,C,pa] using edge
  obtain ⟨u,uu,short,few⟩ := debt.at_cut C affordable
  refine ⟨u,uu,short,lt_of_le_of_lt (Nat.add_le_add_right (card_le_card ?_) _) few⟩
  intro z hz
  obtain ⟨fresh,off⟩ := mem_sdiff.mp hz
  obtain ⟨head,miss⟩ := mem_sdiff.mp fresh
  obtain ⟨zu,pz⟩ := mem_outN.mp head
  have uz : D u z ≠ true := fun h => miss (mem_outN.mpr ⟨zu,h⟩)
  refine mem_filter.mpr ⟨zu,pz,uz,?_⟩
  intro path
  have old := walk_sub sub path
  apply off
  refine mem_filter.mpr ⟨fresh,?_,old⟩
  change spare D U t z < (cost z).card
  by_contra! fits
  rw [show q-1 = q-2+1 by omega] at path
  obtain ⟨b,bu,edge,suffix⟩ := first_step path
  have offered : (u,z) ∈ offers D U t p :=
    mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨uu,short⟩,head⟩,uz⟩
  have charged : b ∈ cost z := mem_filter.mpr
    ⟨mem_outN.mpr ⟨bu,sub _ _ edge⟩,u,offered,walk_sub sub suffix⟩
  have kept := of_decide_eq_true (Bool.and_eq_true_iff.mp edge).2
  exact kept (by simpa [C,pz,fits] using charged)

@[aesop safe forward (immediate := [debt,hq]) (rule_sets := [CHGraphFamilies])]
theorem native_pressure {D U q t p} (debt : OwnReturnDebt D U q t p) (hq : 2 ≤ q) :
    ∃ u ∈ U, (outN D U u).card < t ∧
      ((outN D U p \ outN D U u) \ crowded D D U q t p u).card + (outN D U u).card < t := by
  have same : cut D (fun _ => ∅) = D := by funext a b; simp [cut]
  simpa only [same] using pressure debt hq (fun _ => ∅) (by simp) (by simp)

ch_family_split_result native_pressure

/-- If every deficient row lacks one head, a single physical row has every
missing option crowded. The premise supplies a genuine option on that row. -/
theorem unit_pressure {D U q t p} (debt : OwnReturnDebt D U q t p) (hq : 2 ≤ q)
    (unit : ∀ u ∈ U, (outN D U u).card < t →
      (outN D U u).card + 1 = t ∧ (outN D U p \ outN D U u).Nonempty)
    (L : ℕ → Finset ℕ) (budget : ∀ a ∈ U, (L a).card ≤ spare D U t a)
    (untouched : ∀ a, D p a = true → L a = ∅) :
    ∃ u ∈ U, (outN D U u).card + 1 = t ∧ (outN D U p \ outN D U u).Nonempty ∧
      outN D U p \ outN D U u ⊆ crowded D (cut D L) U q t p u := by
  obtain ⟨u,uu,short,few⟩ := pressure debt hq L budget untouched
  obtain ⟨one,existsHead⟩ := unit u uu short
  refine ⟨u,uu,one,existsHead,?_⟩
  apply sdiff_eq_empty_iff_subset.mp
  exact card_eq_zero.mp (by omega)

/-- On the smallest surviving order band, the actual labelled source supplies
both premises of the unit-deficit result, also after a chosen affordable pre-cut. -/
theorem floor_pressure {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (hq : 2 ≤ q) (none : NoHost q (r-1)) (cell : Marked X m)
    (band : X.V.card = q*(r-1)+2) (L : ℕ → Finset ℕ)
    (budget : ∀ a ∈ X.V \ m.bank, (L a).card ≤ spare X.D (X.V \ m.bank) (r-1) a)
    (untouched : ∀ a, X.D m.parent a = true → L a = ∅) :
    let U := X.V \ m.bank
    ∃ u ∈ U, (outN X.D U u).card + 1 = r-1 ∧ (outN X.D U m.parent \ outN X.D U u).Nonempty ∧
      outN X.D U m.parent \ outN X.D U u ⊆ crowded X.D (cut X.D L) U q (r-1) m.parent u := by
  apply unit_pressure (marked_debt hq none cell (shared_at_floor cell band)) hq _ L budget untouched
  intro u uu short
  obtain ⟨row,native,feeds⟩ := band_all cell band u uu short
  have pv := cell.sub cell.erased
  obtain ⟨z,zu,pz,uz⟩ := candidate_exists X.free (by omega) pv (feeds _ cell.erased)
    (native.le.trans (X.degree _ pv)) (fun h hb _ => feeds h hb)
  exact ⟨by omega,z,mem_sdiff.mpr ⟨mem_outN.mpr ⟨zu,pz⟩,fun old => uz (mem_outN.mp old).2⟩⟩

/-- Each row outside p's heads cuts all its arcs into deficient rows when it
can afford that whole set. The heads of p keep their full first-hop budgets. -/
def trimLast (D : CH.Digraph) (U : Finset ℕ) (t p y : ℕ) : Finset ℕ :=
  let last := outN D (U.filter (fun v => (outN D U v).card < t)) y
  if D p y ≠ true ∧ last.card ≤ spare D U t y then last else ∅

theorem trim_budget {D U t p} (y : ℕ) : (trimLast D U t p y).card ≤ spare D U t y := by
  simp only [trimLast]
  split <;> simp_all

structure BothEnds (D : CH.Digraph) (U : Finset ℕ) (q t p u z : ℕ) : Prop where
  first_budget : spare D U t z < (bill (cut D (trimLast D U t p)) U q (offers D U t p) z).card
  trace : ∃ b ∈ U, ∃ y ∈ U, D z b = true ∧ Walk (cut D (trimLast D U t p)) U b y (q-3) ∧
    D y u = true ∧ spare D U t y < (outN D (U.filter (fun v => (outN D U v).card < t)) y).card

theorem both_ends {D V U q t p u z} (free : QFree D V q) (hq : 3 ≤ q)
    (uv : U ⊆ V) (pv : p ∈ V) (uu : u ∈ U) (short : (outN D U u).card < t)
    (up : D u p = true) (crowd : z ∈ crowded D (cut D (trimLast D U t p)) U q t p u) :
    BothEnds D U q t p u z := by
  classical
  obtain ⟨_,first,path⟩ := mem_filter.mp crowd
  refine ⟨first,?_⟩
  rw [show q-1 = q-3+1+1 by omega] at path
  obtain ⟨b,bu,zb,rest⟩ := first_step path
  obtain ⟨y,middle,_,last⟩ := rest.unsnoc
  have ys := middle.end_mem_or.elim (fun eq => eq ▸ bu) id
  have yu := cut_sub _ _ last
  have off : D p y ≠ true := fun py => free p 3 (by omega) hq
    (.step (uv ys) py (.step (uv uu) yu (.step pv up (.refl _))))
  refine ⟨b,bu,y,ys,cut_sub _ _ zb,middle,yu,?_⟩
  by_contra! fits
  have hit : u ∈ outN D (U.filter (fun v => (outN D U v).card < t)) y :=
    mem_outN.mpr ⟨mem_filter.mpr ⟨uu,short⟩,yu⟩
  exact (of_decide_eq_true (Bool.and_eq_true_iff.mp last).2) (by simp [trimLast,off,fits,hit])

theorem floor_two_ends {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (hq : 3 ≤ q) (none : NoHost q (r-1)) (cell : Marked X m)
    (band : X.V.card = q*(r-1)+2) :
    let U := X.V \ m.bank
    ∃ u ∈ U, (outN X.D U u).card + 1 = r-1 ∧ (outN X.D U m.parent \ outN X.D U u).Nonempty ∧
      ∀ z ∈ outN X.D U m.parent \ outN X.D U u, BothEnds X.D U q (r-1) m.parent u z := by
  let U := X.V \ m.bank
  obtain ⟨u,uu,one,existsHead,crowd⟩ := floor_pressure (by omega : 2 ≤ q) none cell band
    (trimLast X.D U (r-1) m.parent) (fun a _ => trim_budget a)
    (fun a head => by simp [trimLast,head])
  change (outN X.D U u).card + 1 = r-1 at one
  have short : (outN X.D U u).card < r-1 := by omega
  exact ⟨u,uu,one,existsHead,fun z hz => both_ends X.free hq sdiff_subset
    (cell.sub cell.erased) uu short ((shared_at_floor cell band).all_short u uu short) (crowd hz)⟩

#print axioms both_ends
#print axioms floor_two_ends
#print axioms unit_pressure
#print axioms floor_pressure
#print axioms pressure
#print axioms native_pressure
#print axioms safe_iff_cuts_bills
#print axioms overloaded
#print axioms safe_iff_covers_ends
#print axioms paid_end_cover
end LeanCH.BR.SharedParentFirstHops
