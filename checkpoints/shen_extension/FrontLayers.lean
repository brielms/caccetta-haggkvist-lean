import checkpoints.shen_extension.ExcessStepFront

/-!
# Any number of full layers in front of a wide layer

Layers `L 1, …, L h` of width `r`, then `Y = L (h+1)` of width `r + 1`, then
`Z = L (h+2)` of width at most `r - 1`, in a `q`-free graph. Rows of layer `i`
(`1 ≤ i ≤ h + 1`) have out-degree at least `r` and head only layers `1 … i + 1`;
every row of layer `i + 1` (`1 ≤ i ≤ h`) has a parent in layer `i`. These are the
facts `ShapeClimbRoot.head_mem`, `ShapeClimbRoot.parent_mem` of ball layers.
Disjointness of the layers is not needed.

* `chain_walk`: a sink of `L m` that heads all of `L (m+1)` reaches every row of
  `L k` (`m < k ≤ h + 1`) in exactly `k - m` steps, along parents.
* `close_return`: an arc from `L k` back into `L m` closes a walk of length at most
  `r + k - m` (sink path inside `L m`, then the parent chain).
* `full_prefix`: for `r + h ≤ q + 1`, every row of `L k` (`1 ≤ k ≤ h`) heads only
  `L k ∪ L (k+1)`, and every sink of `L k` (`k < h`) heads all of `L (k+1)`.
* `front_false`: for `r + h ≤ q`, `3 ≤ r`, `1 ≤ h` the shape is impossible.

Generic in `r`, `q`, `h`.
-/

namespace LeanCH.BR.FrontLayers
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn TightLayerShapes

/-- The layer hypotheses, in the form of `ShapeClimbRoot.head_mem` / `parent_mem`. -/
structure Layers (D : CH.Digraph) (V : Finset ℕ) (L : ℕ → Finset ℕ) (q r h : ℕ) : Prop where
  free : QFree D V q
  sub : ∀ i, L i ⊆ V
  size : ∀ i, 1 ≤ i → i ≤ h → (L i).card = r
  quota : ∀ i, 1 ≤ i → i ≤ h + 1 → ∀ v ∈ L i, r ≤ (outN D V v).card
  step : ∀ i, 1 ≤ i → i ≤ h + 1 → ∀ v ∈ L i, ∀ x ∈ outN D V v, ∃ j, 1 ≤ j ∧ j ≤ i + 1 ∧ x ∈ L j
  parent : ∀ i, 1 ≤ i → i ≤ h → ∀ y ∈ L (i + 1), ∃ p ∈ L i, D p y = true

variable {D : CH.Digraph} {V : Finset ℕ} {L : ℕ → Finset ℕ} {q r h : ℕ}

/-- **Parent chain.** A row `σ` heading all of `L (m+1)` reaches every row of `L k`,
`m < k ≤ h + 1`, in exactly `k - m` steps. -/
theorem chain_walk (P : Layers D V L q r h) {m k σ x : ℕ} (hm : 1 ≤ m) (mk : m < k)
    (kh : k ≤ h + 1) (full : L (m + 1) ⊆ outN D V σ) (xm : x ∈ L k) :
    Walk D V σ x (k - m) := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
    by_cases e : k = m
    · subst e
      simpa only [Nat.add_sub_cancel_left] using
        (Walk.step (P.sub _ xm) (mem_outN.mp (full xm)).2 (.refl x) : Walk D V σ x 1)
    obtain ⟨p, pm, px⟩ := P.parent k (by omega) (by omega) x xm
    have w := ih (by omega) (by omega) pm
    simpa only [show k + 1 - m = k - m + 1 by omega] using w.snoc (P.sub _ xm) px

/-- **Return.** If every sink of `L m` heads all of `L (m+1)`, an arc from a row of
`L k` (`m < k ≤ h + 1`) back into `L m` closes a walk of length at most `r + k - m`. -/
theorem close_return (P : Layers D V L q r h) {m k u x : ℕ} (hm : 1 ≤ m) (mk : m < k)
    (kh : k ≤ h + 1) (cm : (L m).card ≤ r) (rq : r ≤ q)
    (full : ∀ s ∈ L m, Sink D (L m) s → L (m + 1) ⊆ outN D V s)
    (len : r + k ≤ q + m) (um : u ∈ L m) (xm : x ∈ L k) (ret : D x u = true) : False := by
  obtain ⟨s, sm, stop, l, ll, walk⟩ :=
    reach_sink_of_card ((P.free.mono_set (P.sub m))) (cm.trans rq) um
  have tail := chain_walk P hm mk kh (full s sm (fun z zm => stop z zm)) xm
  have loop := ((walk.mono (P.sub m)).append tail).snoc (P.sub m um) ret
  exact P.free u _ (by omega) (by omega) loop

/-- **Full prefix.** For `r + h ≤ q + 1`, the rows of `L k`, `1 ≤ k ≤ h`, head only
`L k ∪ L (k+1)`. -/
theorem full_prefix (P : Layers D V L q r h) (time : r + h ≤ q + 1) :
    ∀ k, 1 ≤ k → k ≤ h → ∀ v ∈ L k, outN D V v ⊆ L k ∪ L (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk kh v vm x xm
    obtain ⟨j, hj, jk, xj⟩ := P.step k hk (by omega) v vm x xm
    by_cases e : j = k + 1
    · exact mem_union_right _ (e ▸ xj)
    by_cases e' : j = k
    · exact mem_union_left _ (e' ▸ xj)
    have full (s) (sm : s ∈ L j) (ks : Sink D (L j) s) : L (j + 1) ⊆ outN D V s :=
      sink_full (ih j (by omega) hj (by omega) s sm) ks (P.quota j hj (by omega) s sm)
        (P.size (j + 1) (by omega) (by omega))
    exact (close_return P hj (by omega : j < k) (by omega) (P.size j hj (by omega)).le
      (by omega) full (by omega) xj vm (mem_outN.mp xm).2).elim

/-- Every sink of `L k`, `1 ≤ k < h`, heads all of `L (k+1)`. -/
theorem sinks_full (P : Layers D V L q r h) (time : r + h ≤ q + 1) {k : ℕ} (hk : 1 ≤ k)
    (kh : k < h) : ∀ s ∈ L k, Sink D (L k) s → L (k + 1) ⊆ outN D V s :=
  fun s sm ks => sink_full (full_prefix P time k hk kh.le s sm) ks
    (P.quota k hk (by omega) s sm) (P.size (k + 1) (by omega) (by omega))

/-- **No far return.** For `r + h ≤ q + 1`, a row of `L k` (`k ≤ h + 1`) has no head
in `L m` with `1 ≤ m < k`, `m < h`, as soon as `r + k ≤ q + m`. -/
theorem no_far_return (P : Layers D V L q r h) (time : r + h ≤ q + 1) {m k u x : ℕ}
    (hm : 1 ≤ m) (mk : m < k) (mh : m < h) (kh : k ≤ h + 1) (len : r + k ≤ q + m)
    (um : u ∈ L m) (xm : x ∈ L k) (ret : D x u = true) : False :=
  close_return P hm mk kh (P.size m hm mh.le).le (by omega) (sinks_full P time hm mh) len um xm ret

/-- **Front, any height.** `h ≥ 1` full layers of width `r`, then `r + 1`, then at most
`r - 1`, with `3 ≤ r` and `r + h ≤ q`: impossible. -/
theorem front_false (P : Layers D V L q r h) (hh : 1 ≤ h) (three : 3 ≤ r) (time : r + h ≤ q)
    (cy : (L (h + 1)).card = r + 1) (cz : (L (h + 2)).card + 1 ≤ r) : False := by
  classical
  apply wide_false (X := L h) (Y := L (h + 1)) (three := three)
  refine ⟨P.free, P.sub h, P.sub (h + 1), P.size h hh le_rfl, cy, by omega,
    P.quota h hh (by omega), full_prefix P (by omega) h hh le_rfl, ?_⟩
  intro t tm kt
  by_contra! none
  have sub : outN D V t ⊆ L (h + 2) := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    obtain ⟨j, hj, jle, zj⟩ := P.step (h + 1) (by omega) le_rfl t tm z hz
    by_cases e : j = h + 2
    · exact e ▸ zj
    by_cases e' : j = h + 1
    · exact (kt z (e' ▸ zj) arc).elim
    by_cases e'' : j = h
    · exact (none z (e'' ▸ zj) arc).elim
    exact (no_far_return P (by omega) hj (by omega : j < h + 1) (by omega) le_rfl (by omega)
      zj tm arc).elim
  have := card_le_card sub
  have := P.quota (h + 1) (by omega) le_rfl t tm
  omega

#print axioms chain_walk
#print axioms close_return
#print axioms full_prefix
#print axioms front_false

/-- **No return into the first layer, tight.** For `3 ≤ h`, `3 ≤ r` and `r + h ≤ q + 1`,
a row `t` of `L (h+1)` has no head in `L 1`. A return target `u` is `(q - h)`-deep in
`L 1` (route `L 1`-sink ⇝ `t` along parents, `h` arcs), so it has at most one head in
`L 1`; each head `w` of `u` in `L 2` is `(q - h)`-deep in `L 2` (route `L 2`-sink ⇝ `t`
⇝ `u`, `h` arcs), and at most one row of `L 2` is. So `u` has at most two heads. -/
theorem tight_no_return (P : Layers D V L q r h) (h3 : 3 ≤ h) (three : 3 ≤ r)
    (time : r + h ≤ q + 1) {t u : ℕ} (tm : t ∈ L (h + 1)) (um : u ∈ L 1)
    (ret : D t u = true) : False := by
  classical
  have c1 := P.size 1 le_rfl (by omega)
  have c2 := P.size 2 (by omega) (by omega)
  have f1 := P.free.mono_set (P.sub 1)
  have f2 := P.free.mono_set (P.sub 2)
  have tV := P.sub _ tm
  -- `u` is `(q - h)`-deep in `L 1`
  have deep1 : Deep D (L 1) (q - h) u := return_deep P.free (P.sub 1) um (fun s sm ks => by
    have w := chain_walk P le_rfl (by omega : 1 < h + 1) le_rfl
      (sinks_full P time le_rfl (by omega) s sm ks) tm
    simpa only [Nat.add_sub_cancel] using w) ret
  have in1 := deep_heads f1 (by omega) um deep1
  -- heads of `u` in `L 2` are `(q - h)`-deep in `L 2`
  have in2 : outN D (L 2) u ⊆ (L 2).filter (Deep D (L 2) (q - h)) := by
    intro w hw
    obtain ⟨wm, uw⟩ := mem_outN.mp hw
    refine mem_filter.mpr ⟨wm, return_deep P.free (P.sub 2) wm (fun s sm ks => ?_) uw⟩
    have w' := chain_walk P (by omega : 1 ≤ 2) (by omega : 2 < h + 1) le_rfl
      (sinks_full P time (by omega) (by omega) s sm ks) tm
    have := w'.snoc (P.sub 1 um) ret
    simpa only [show h + 1 - 2 + 1 = h by omega] using this
  have few : ((L 2).filter (Deep D (L 2) (q - h))).card ≤ 1 := by
    rcases deep_card (t := q - h) f2 (by omega) with bound | empty
    · omega
    · rw [empty]; simp
  have split : outN D V u ⊆ outN D (L 1) u ∪ outN D (L 2) u := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (full_prefix P time 1 le_rfl (by omega) u um hz) with z1 | z2
    · exact mem_union_left _ (mem_outN.mpr ⟨z1, arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨z2, arc⟩)
  have := (card_le_card split).trans (card_union_le _ _)
  have := card_le_card in2
  have := P.quota 1 le_rfl (by omega) u um
  omega

/-- **Front, any height, tight.** `h ≥ 2` full layers of width `r`, then `r + 1`, then at
most `r - 1`, with `3 ≤ r` and `r + h ≤ q + 1`: impossible. For `h = 2` this is
`full_front_tight_false`; for `h ≥ 3` every return from `L (h+1)` into `L 1 … L (h-1)`
is excluded and `wide_false` applies. (At `h = 1` the bound `r + 1 ≤ q + 1` is false:
the wide shape has models at `q = r`.) -/
theorem front_tight_false (P : Layers D V L q r h) (hh : 2 ≤ h) (three : 3 ≤ r)
    (time : r + h ≤ q + 1) (cy : (L (h + 1)).card = r + 1) (cz : (L (h + 2)).card + 1 ≤ r) :
    False := by
  classical
  by_cases two : h = 2
  · subst two
    have headsX (x) (xm : x ∈ L 2) : outN D V x ⊆ L 1 ∪ L 2 ∪ L 3 := by
      intro z hz
      obtain ⟨j, hj, jle, zj⟩ := P.step 2 (by omega) (by omega) x xm z hz
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl
      · exact mem_union_left _ (mem_union_left _ zj)
      · exact mem_union_left _ (mem_union_right _ zj)
      · exact mem_union_right _ zj
    have headsY (y) (ym : y ∈ L 3) : outN D V y ⊆ L 1 ∪ L 2 ∪ L 3 ∪ L 4 := by
      intro z hz
      obtain ⟨j, hj, jle, zj⟩ := P.step 3 (by omega) (by omega) y ym z hz
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ zj))
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ zj))
      · exact mem_union_left _ (mem_union_right _ zj)
      · exact mem_union_right _ zj
    exact full_front_tight_false P.free (P.sub 1) (P.sub 2) (P.sub 3)
      (P.size 1 le_rfl (by omega)) (P.size 2 (by omega) le_rfl) cy cz three (by omega)
      (P.quota 1 le_rfl (by omega)) (P.quota 2 (by omega) (by omega)) (P.quota 3 (by omega) le_rfl)
      (full_prefix P time 1 le_rfl (by omega)) headsX headsY (P.parent 2 (by omega) le_rfl)
  apply wide_false (X := L h) (Y := L (h + 1)) (three := three)
  refine ⟨P.free, P.sub h, P.sub (h + 1), P.size h (by omega) le_rfl, cy, by omega,
    P.quota h (by omega) (by omega), full_prefix P time h (by omega) le_rfl, ?_⟩
  intro t tm kt
  by_contra! none
  have sub : outN D V t ⊆ L (h + 2) := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    obtain ⟨j, hj, jle, zj⟩ := P.step (h + 1) (by omega) le_rfl t tm z hz
    by_cases e : j = h + 2
    · exact e ▸ zj
    by_cases e' : j = h + 1
    · exact (kt z (e' ▸ zj) arc).elim
    by_cases e'' : j = h
    · exact (none z (e'' ▸ zj) arc).elim
    by_cases e1 : j = 1
    · subst e1
      exact (tight_no_return P (by omega) three time tm zj arc).elim
    exact (no_far_return P time hj (by omega : j < h + 1) (by omega) le_rfl (by omega)
      zj tm arc).elim
  have := card_le_card sub
  have := P.quota (h + 1) (by omega) le_rfl t tm
  omega

#print axioms tight_no_return
#print axioms front_tight_false

end LeanCH.BR.FrontLayers
