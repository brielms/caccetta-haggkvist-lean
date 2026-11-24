import checkpoints.shen_extension.TransitionClosure

/-!
# Static form of the delete-and-add closure: least shortfall on a fixed label set

Lean 4.35.0. Own file; no existing file is touched. Paper: `TransitionClosure_Skeleton_20261118.md` (last sections).

Restricted rule list `RStep`: delete vertices or add one safe arc at a short row (no cutting).

* `rstep_originalKept`: every surviving original arc stays present along `RStep`.
* `shortfall_ge_static`: every valid state that keeps its original arcs has shortfall `capTotal - |F|` for an
  admissible family `F` on its labels (kept non-original arcs, at most `cap u` per row).
* `static_reachable`: every admissible family `F` on a nonempty `U ⊆ V` is realised by an `RStep`-reachable state on
  `U` with shortfall exactly `capTotal - |F|`.
* `static_minimum`: so on a fixed label set the least reachable shortfall is `capTotal` minus the largest size of
  an admissible family.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.Closure

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.DeleteRepair

variable {q s : ℕ}

/-! ## Definitions -/

/-- Total shortfall of a state: `∑_{v ∈ U} (s - outdeg v)` (truncated subtraction). -/
def shortfall (s : ℕ) (st : State) : ℕ := ∑ v ∈ st.U, (s - (outN st.H st.U v).card)

/-- Restricted rule list: delete vertices, or add a safe arc at a short row. -/
def RStep (q s : ℕ) (a b : State) : Prop := DeleteStep a b ∨ AddStep q s a b

/-- Every surviving original arc is present. -/
def OriginalKept (O : Origin q s) (st : State) : Prop :=
  ∀ a ∈ st.U, ∀ b ∈ st.U, O.G a b = true → st.H a b = true

/-- Capacity of row `u` on labels `U`: what the original arcs inside `U` leave to reach `s`. -/
def cap (O : Origin q s) (U : Finset ℕ) (u : ℕ) : ℕ := s - (outN O.G U u).card

def capTotal (O : Origin q s) (U : Finset ℕ) : ℕ := ∑ u ∈ U, cap O U u

/-- The original digraph together with the arcs of `F`. -/
def addArcs (G : CH.Digraph) (F : Finset (ℕ × ℕ)) : CH.Digraph := fun a b => G a b || decide ((a, b) ∈ F)

/-- Pairs of `F` with first coordinate `u`. -/
def row (F : Finset (ℕ × ℕ)) (u : ℕ) : Finset (ℕ × ℕ) := F.filter (fun p => p.1 = u)

/-- An admissible family of new arcs on `U`. -/
structure Admissible (O : Origin q s) (U : Finset ℕ) (F : Finset (ℕ × ℕ)) : Prop where
  sub : F ⊆ U ×ˢ U
  new : ∀ p ∈ F, O.G p.1 p.2 ≠ true
  rowCap : ∀ u ∈ U, (row F u).card ≤ cap O U u
  free : QFree (addArcs O.G F) U q

/-! ## Small lemmas -/

theorem walk_sub_on {D E : CH.Digraph} {W : Finset ℕ}
    (h : ∀ a ∈ W, ∀ b ∈ W, D a b = true → E a b = true) {a b m : ℕ}
    (w : Walk D W a b m) : a ∈ W → Walk E W a b m := by
  induction w with
  | refl a => exact fun _ => .refl a
  | step hb hab _ ih => exact fun ha => .step hb (h _ ha _ hb hab) (ih hb)

/-- A sub-digraph on `W` of a `q`-free digraph on `W` is `q`-free. -/
theorem qfree_sub_on {D E : CH.Digraph} {W : Finset ℕ} {q : ℕ}
    (h : ∀ a ∈ W, ∀ b ∈ W, D a b = true → E a b = true) (hf : QFree E W q) : QFree D W q := by
  intro a ℓ h1 hq w
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨_, _, ha, _⟩ := w.unsnoc
  exact hf a (k + 1) h1 hq (walk_sub_on h w ha)

theorem mem_rowImage {F : Finset (ℕ × ℕ)} {u b : ℕ} : b ∈ (row F u).image Prod.snd ↔ (u, b) ∈ F := by
  constructor
  · intro hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hpF, hpu⟩ := Finset.mem_filter.mp hp
    rw [← hpu]
    exact hpF
  · intro hb
    exact Finset.mem_image.mpr ⟨(u, b), Finset.mem_filter.mpr ⟨hb, rfl⟩, rfl⟩

theorem card_rowImage (F : Finset (ℕ × ℕ)) (u : ℕ) : ((row F u).image Prod.snd).card = (row F u).card := by
  apply Finset.card_image_of_injOn
  intro _ hp _ hp' he
  have h1 := (Finset.mem_filter.mp hp).2
  have h2 := (Finset.mem_filter.mp hp').2
  exact Prod.ext (h1.trans h2.symm) he

/-- Row count of `G` plus new arcs `F`: original heads plus the row of `F`. -/
theorem outN_addArcs_card {G : CH.Digraph} {U : Finset ℕ} {F : Finset (ℕ × ℕ)} (hF : F ⊆ U ×ˢ U)
    (hnew : ∀ p ∈ F, G p.1 p.2 ≠ true) (u : ℕ) :
    (outN (addArcs G F) U u).card = (outN G U u).card + (row F u).card := by
  have e : outN (addArcs G F) U u = outN G U u ∪ (row F u).image Prod.snd := by
    ext b
    rw [Finset.mem_union, mem_rowImage, mem_outN, mem_outN]
    simp only [addArcs, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hb, h | h⟩
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr h
    · rintro (⟨hb, h⟩ | h)
      · exact ⟨hb, Or.inl h⟩
      · exact ⟨(Finset.mem_product.mp (hF h)).2, Or.inr h⟩
  have d : Disjoint (outN G U u) ((row F u).image Prod.snd) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    exact hnew _ (mem_rowImage.mp hb') (mem_outN.mp hb).2
  rw [e, Finset.card_union_of_disjoint d, card_rowImage]

theorem sum_tsub_of_le {U : Finset ℕ} {c k : ℕ → ℕ} (h : ∀ v ∈ U, k v ≤ c v) :
    ∑ v ∈ U, (c v - k v) = ∑ v ∈ U, c v - ∑ v ∈ U, k v := by
  have e : ∑ v ∈ U, (c v - k v) + ∑ v ∈ U, k v = ∑ v ∈ U, c v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v hv => Nat.sub_add_cancel (h v hv))
  omega

theorem card_eq_sum_row {U : Finset ℕ} {F : Finset (ℕ × ℕ)} (hF : F ⊆ U ×ˢ U) :
    F.card = ∑ u ∈ U, (row F u).card :=
  Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun _ hp => (Finset.mem_product.mp (hF hp)).1)

/-- Shortfall of the digraph `G ∪ F` on `U`, for `F` admissible. -/
theorem shortfall_addArcs (O : Origin q s) {U : Finset ℕ} {F : Finset (ℕ × ℕ)} (hF : Admissible O U F) :
    shortfall s ⟨U, addArcs O.G F⟩ = capTotal O U - F.card := by
  unfold shortfall capTotal
  rw [card_eq_sum_row hF.sub, ← sum_tsub_of_le hF.rowCap]
  apply Finset.sum_congr rfl
  intro v _
  simp only
  rw [outN_addArcs_card hF.sub hF.new v]
  unfold cap
  omega

/-! ## 1. Original arcs are kept by the restricted rules -/

theorem init_originalKept (O : Origin q s) : OriginalKept O O.init := fun _ _ _ _ h => h

theorem delete_originalKept (O : Origin q s) {a b : State} (h : OriginalKept O a) (d : DeleteStep a b) :
    OriginalKept O b := by
  obtain ⟨hH, hU, _⟩ := d
  intro x hx y hy hxy
  rw [hH]
  exact h x (hU.subset hx) y (hU.subset hy) hxy

theorem add_originalKept (O : Origin q s) {a b : State} (h : OriginalKept O a) (ad : AddStep q s a b) :
    OriginalKept O b := by
  obtain ⟨_, _, _, _, _, _, hU, hH⟩ := ad
  intro x hx y hy hxy
  rw [hH]
  rw [hU] at hx hy
  exact repair_old (h x hx y hy hxy)

/-- **Every `RStep`-reachable state keeps all its surviving original arcs.** -/
theorem rstep_originalKept (O : Origin q s) {st : State} (r : Reach (RStep q s) O.init st) :
    OriginalKept O st :=
  invariant_of_reach (inv := OriginalKept O)
    (fun _ _ h st' => st'.elim (delete_originalKept O h) (add_originalKept O h)) (init_originalKept O) r

theorem rreach_reach {a b : State} (r : Reach (RStep q s) a b) : Reach (Step q s) a b := by
  induction r with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.tail (h.elim Step.delete Step.add)

theorem rreach_valid (O : Origin q s) {st : State} (r : Reach (RStep q s) O.init st) : Valid O st :=
  reach_valid O (rreach_reach r)

/-! ## 2. Lower bound -/

/-- Non-original heads of `u` in the state. -/
def extraHeads (O : Origin q s) (st : State) (u : ℕ) : Finset ℕ :=
  (outN st.H st.U u).filter (fun b => ¬ O.G u b = true)

theorem outN_split (O : Origin q s) {st : State} (kept : OriginalKept O st) {u : ℕ} (hu : u ∈ st.U) :
    (outN st.H st.U u).card = (outN O.G st.U u).card + (extraHeads O st u).card := by
  have e : (outN st.H st.U u).filter (fun b => O.G u b = true) = outN O.G st.U u := by
    ext b
    rw [Finset.mem_filter, mem_outN, mem_outN]
    exact ⟨fun ⟨⟨hb, _⟩, h⟩ => ⟨hb, h⟩, fun ⟨hb, h⟩ => ⟨⟨hb, kept u hu b hb h⟩, h⟩⟩
  rw [← e, extraHeads]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- **Lower bound.** Every valid state keeping its original arcs has shortfall `capTotal - |F|` for an admissible
family `F` on its labels. -/
theorem shortfall_ge_static (O : Origin q s) {st : State} (v : Valid O st) (kept : OriginalKept O st) :
    ∃ F, Admissible O st.U F ∧ shortfall s st = capTotal O st.U - F.card ∧ F.card ≤ capTotal O st.U := by
  have hex : ∀ u, ∃ T ⊆ extraHeads O st u, T.card = min (extraHeads O st u).card (cap O st.U u) :=
    fun u => Finset.exists_subset_card_eq (min_le_left _ _)
  choose T hT hTc using hex
  have hTmem : ∀ {u b}, b ∈ T u → b ∈ st.U ∧ st.H u b = true ∧ ¬ O.G u b = true := by
    intro u b hb
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (hT u hb)
    exact ⟨(mem_outN.mp h1).1, (mem_outN.mp h1).2, h2⟩
  let F : Finset (ℕ × ℕ) := (st.U ×ˢ st.U).filter (fun p => p.2 ∈ T p.1)
  have memF : ∀ {a b}, (a, b) ∈ F ↔ a ∈ st.U ∧ b ∈ T a := by
    intro a b
    simp only [F, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun ⟨⟨ha, _⟩, h⟩ => ⟨ha, h⟩, fun ⟨ha, h⟩ => ⟨⟨ha, (hTmem h).1⟩, h⟩⟩
  have hsub : F ⊆ st.U ×ˢ st.U := Finset.filter_subset _ _
  have hnew : ∀ p ∈ F, O.G p.1 p.2 ≠ true := by
    rintro ⟨a, b⟩ hp
    exact (hTmem (memF.mp hp).2).2.2
  have rowEq : ∀ u ∈ st.U, (row F u).card = (T u).card := by
    intro u hu
    rw [← card_rowImage]
    congr 1
    ext b
    rw [mem_rowImage, memF]
    exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
  have adm : Admissible O st.U F := by
    refine ⟨hsub, hnew, ?_, ?_⟩
    · intro u hu
      rw [rowEq u hu, hTc]
      exact min_le_right _ _
    · apply qfree_sub_on _ v.2.2
      intro a ha b _ hab
      simp only [addArcs, Bool.or_eq_true, decide_eq_true_eq] at hab
      rcases hab with h | h
      · exact kept a ha b (by assumption) h
      · exact (hTmem (memF.mp h).2).2.1
  refine ⟨F, adm, ?_, ?_⟩
  · unfold shortfall capTotal
    rw [card_eq_sum_row hsub, ← sum_tsub_of_le adm.rowCap]
    apply Finset.sum_congr rfl
    intro u hu
    rw [outN_split O kept hu, rowEq u hu, hTc]
    unfold cap
    omega
  · rw [card_eq_sum_row hsub, capTotal]
    exact Finset.sum_le_sum adm.rowCap

/-! ## 3. Achievability -/

theorem addArcs_insert (G : CH.Digraph) (S : Finset (ℕ × ℕ)) (u z : ℕ) :
    addArcs G (insert (u, z) S) = repair (addArcs G S) {u} (fun _ => {z}) := by
  funext a b
  simp only [addArcs, repair, Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton]
  by_cases h1 : a = u <;> by_cases h2 : b = z <;> simp [h1, h2]

theorem addArcs_mono {G : CH.Digraph} {S F : Finset (ℕ × ℕ)} (h : S ⊆ F) :
    ∀ a b, addArcs G S a b = true → addArcs G F a b = true := by
  intro a b hab
  simp only [addArcs, Bool.or_eq_true, decide_eq_true_eq] at hab ⊢
  exact hab.imp_right (fun x => h x)

/-- Adding the arcs of `F` one at a time: every subfamily is reached from `⟨U, G⟩`. -/
theorem add_family (O : Origin q s) {U : Finset ℕ} {F : Finset (ℕ × ℕ)} (hF : Admissible O U F) :
    ∀ S ⊆ F, Reach (RStep q s) ⟨U, O.G⟩ ⟨U, addArcs O.G S⟩ := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have : addArcs O.G ∅ = O.G := by funext a b; simp [addArcs]
    rw [this]
  | @insert p S hp ih =>
    intro hsub
    have hS : S ⊆ F := (Finset.subset_insert p S).trans hsub
    have hpF : p ∈ F := hsub (Finset.mem_insert_self p S)
    obtain ⟨u, z⟩ := p
    obtain ⟨hu, hz⟩ := Finset.mem_product.mp (hF.sub hpF)
    refine (ih hS).tail (Or.inr ⟨u, z, ⟨hu, ?_⟩, hz, ?_, ?_, rfl, addArcs_insert O.G S u z⟩)
    · -- row `u` is short: it has fewer heads than in the final digraph, which has at most `s`
      have hSsub : S ⊆ U ×ˢ U := hS.trans hF.sub
      have hSnew : ∀ p ∈ S, O.G p.1 p.2 ≠ true := fun p hp' => hF.new p (hS hp')
      rw [outN_addArcs_card hSsub hSnew u]
      have lt : (row S u).card < (row F u).card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset_filter _ hS, fun h => hp ?_⟩
        exact (Finset.mem_filter.mp (h (Finset.mem_filter.mpr ⟨hpF, rfl⟩))).1
      have := hF.rowCap u hu
      unfold cap at this
      omega
    · intro h
      simp only [addArcs, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact hF.new _ hpF h
      · exact hp h
    · -- `z` does not return to `u` quickly: that would close a short walk in the final digraph
      intro m hm w
      have w' := walk_sub (addArcs_mono hS) w
      have arc : addArcs O.G F u z = true := by
        simp only [addArcs, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr hpF
      have closed : Walk (addArcs O.G F) U u u (m + 1) := by
        exact Walk.step hz arc w'
      exact hF.free u (m + 1) (by omega) hm closed

/-- **Achievability.** Every admissible family on a nonempty `U ⊆ V` is realised by a reachable state. -/
theorem static_reachable (O : Origin q s) {U : Finset ℕ} (hU : U ⊆ O.V) (hne : U.Nonempty)
    {F : Finset (ℕ × ℕ)} (hF : Admissible O U F) :
    ∃ t, Reach (RStep q s) O.init t ∧ t.U = U ∧ OriginalKept O t ∧ shortfall s t = capTotal O U - F.card := by
  have start : Reach (RStep q s) O.init ⟨U, O.G⟩ := by
    rcases hU.eq_or_ssubset with h | h
    · rw [h]; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (Or.inl ⟨rfl, h, hne⟩)
  refine ⟨⟨U, addArcs O.G F⟩, start.trans (add_family O hF F (Finset.Subset.refl F)), rfl, ?_,
    shortfall_addArcs O hF⟩
  intro a _ b _ h
  simp [addArcs, h]

/-! ## 4. The static minimum -/

/-- **Static minimum.** On a fixed nonempty `U ⊆ V`, the reachable shortfalls are exactly `capTotal - |F|` over
admissible families `F`: every reachable state on `U` has shortfall at least (indeed equal to) `capTotal - |F|`
for some admissible `F`, and every admissible `F` is attained. -/
theorem static_minimum (O : Origin q s) {U : Finset ℕ} (hU : U ⊆ O.V) (hne : U.Nonempty) :
    (∀ t, Reach (RStep q s) O.init t → t.U = U →
        ∃ F, Admissible O U F ∧ capTotal O U - F.card ≤ shortfall s t) ∧
    (∀ F, Admissible O U F →
        ∃ t, Reach (RStep q s) O.init t ∧ t.U = U ∧ shortfall s t = capTotal O U - F.card) := by
  refine ⟨?_, ?_⟩
  · intro t r ht
    obtain ⟨F, adm, eq, _⟩ := shortfall_ge_static O (rreach_valid O r) (rstep_originalKept O r)
    rw [ht] at adm eq
    exact ⟨F, adm, eq.ge⟩
  · intro F hF
    obtain ⟨t, r, ht, _, eq⟩ := static_reachable O hU hne hF
    exact ⟨t, r, ht, eq⟩

end LeanCH.BR.Closure

open LeanCH.BR.Closure in
#print axioms rstep_originalKept
open LeanCH.BR.Closure in
#print axioms shortfall_ge_static
open LeanCH.BR.Closure in
#print axioms static_reachable
open LeanCH.BR.Closure in
#print axioms static_minimum
