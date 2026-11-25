import checkpoints.shen_extension.SinkDepthReturn
import checkpoints.shen_extension.EqualLayerTransit
import checkpoints.shen_extension.FifthStripAllParity

/-!
# Flat layers persist up to height `q - 1` (funnel growth)

`flat_persist` is `EqualLayerTransit.end_capacity` with the height condition
`r/2 + h ≤ q` replaced by `h + 1 ≤ q` (sharp by SAT).

Proof (funnel growth). By strong induction no row of `L i` has a head in an earlier layer.
Suppose `x ∈ L i` heads `y ∈ L j`, `j < i`; put `t = i - j`, `a = q - t ≥ 2`.
The funnel `G m` is the set of rows of `L m` reached from `y` by a walk of length `m - j`.

* `squeeze`: rows of `G m` (`j ≤ m < i`) are `a`-deep in `L m`, since a sink of `L m`
  reaches `x` in `i - m` steps (`from_sink`) and `x → y`.
* `head_deep` (D1): a head inside `X` of a `t+1`-deep row is `t`-deep.
* growth: a sink of `G m` (inside `G m`) has all its in-layer heads `(a-1)`-deep and outside
  `G m`, and its heads in `L (m+1)` inside `G (m+1)`; with `deep_card` this gives
  `|G m| + (a-1) ≤ |G (m+1)|`.
* hence `t ≤ |G (i-1)|`, while `deep_card` gives `|G (i-1)| + a ≤ r`, so `q = t + a ≤ r`.

`flat_root_persist` is `FifthStripAllParity.flat_root_false` without the hypothesis `height`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FlatPersist
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors SinkDepthReturn

/-- **Squeeze.** If every `X`-sink reaches `y` within `M ≥ 1` steps and `y` reaches `z ∈ X`
within `ℓ` steps, then `z` is `(q + 1 - ℓ - M)`-deep in `X`. -/
theorem squeeze {D V X q y z ℓ M} (free : QFree D V q) (xv : X ⊆ V) (hM : 1 ≤ M)
    (yz : Walk D V y z ℓ) (reach : ∀ s ∈ X, Sink D X s → Walk D V s y M) :
    Deep D X (q + 1 - ℓ - M) z := by
  intro s sm stop k walk
  by_contra! short
  have loop := (yz.append (walk.mono xv)).append (reach s sm stop)
  exact free y (ℓ + k + M) (by omega) (by omega) loop

/-- **D1.** A head inside `X` of a `(t+1)`-deep row is `t`-deep. -/
theorem head_deep {D X t z w} (deep : Deep D X (t + 1) z) (wm : w ∈ X) (arc : D z w = true) :
    Deep D X t w := by
  intro s sm stop k walk
  have := deep s sm stop (k + 1) (Walk.step wm arc walk)
  omega

open scoped Classical in
/-- `deep_card` for a nonempty subset of deep rows. -/
theorem deep_card_of {D X q t} {G : Finset ℕ} (free : QFree D X q) (size : X.card ≤ q)
    (gx : G ⊆ X) (deep : ∀ z ∈ G, Deep D X t z) (ne : G.Nonempty) : t + G.card ≤ X.card := by
  have gk : G ⊆ X.filter (Deep D X t) := fun z zm => mem_filter.mpr ⟨gx zm, deep z zm⟩
  rcases deep_card (t := t) free size with bound | empty
  · have := card_le_card gk
    omega
  · obtain ⟨z, zm⟩ := ne
    have := gk zm
    rw [empty] at this
    simp at this

/-- Funnel growth inside one layer: a nonempty set `G ⊆ X` of `a`-deep rows (`a ≥ 1`) whose
heads all lie in `X ∪ Y`, with heads in `Y` inside `G'`, satisfies `|G| + (a-1) ≤ |G'|`. -/
theorem growth {V X Y G G' : Finset ℕ} {q r a : ℕ} {D : CH.Digraph}
    (free : QFree D V q) (xv : X ⊆ V) (size : X.card = r) (rq : r ≤ q) (ha : 1 ≤ a)
    (gx : G ⊆ X) (ne : G.Nonempty) (deep : ∀ z ∈ G, Deep D X a z)
    (quota : ∀ z ∈ G, r ≤ (outN D V z).card)
    (keep : ∀ z ∈ G, outN D V z ⊆ X ∪ Y)
    (next : ∀ z ∈ G, ∀ w ∈ Y, D z w = true → w ∈ G') : G.card + (a - 1) ≤ G'.card := by
  classical
  have fx : QFree D X q := free.mono_set xv
  have gq : G.card ≤ q := (card_le_card gx).trans (size ▸ rq)
  obtain ⟨s, sm, stop⟩ := exists_sink (free.mono_set (gx.trans xv)) ne gq
  let K := X.filter (Deep D X (a - 1))
  have gk : G ⊆ K := fun z zm => mem_filter.mpr ⟨gx zm, (deep z zm).mono (by omega)⟩
  have cover : outN D V s ⊆ (K \ G) ∪ G' := by
    intro w wm
    have arc := (mem_outN.mp wm).2
    rcases mem_union.mp (keep s sm wm) with wx | wy
    · refine mem_union_left _ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨wx, ?_⟩, fun wg => stop w wg arc⟩)
      exact head_deep (t := a - 1) ((deep s sm).mono (by omega)) wx arc
    · exact mem_union_right _ (next s sm w wy arc)
  have c1 := (quota s sm).trans ((card_le_card cover).trans (card_union_le _ _))
  have c2 := card_sdiff_add_card_eq_card gk
  have bound := deep_card_of (G := K) (t := a - 1) fx (size ▸ rq) (filter_subset _ _)
    (fun z zm => (mem_filter.mp zm).2) ⟨s, gk sm⟩
  rw [size] at bound
  omega

/-- **Flat layers persist.** `end_capacity` with `r/2 + h ≤ q` weakened to `h + 1 ≤ q`. -/
theorem flat_persist {D V q r h} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r < q) (time : h + 1 ≤ q) (depth : 0 < h)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < h → (L i).card=r)
    (_apart : ∀ (i : ℕ),  i+1 < h → Disjoint (L i) (L (i+1)))
    (quota : ∀ (i : ℕ), i < h → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i < h → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j) :
    r ≤ (L h).card := by
  classical
  have sinks {i} (hi : i < h) (hi' : i+1 < h)
      (keep : ∀v∈L i,outN D V v⊆L i∪L (i+1)) (s) (sm : s∈L i) (last : Sink D (L i) s) :
      L (i+1)⊆outN D V s := by
    apply (eq_of_subset_of_card_le (s:=outN D V s) (t:=L (i+1)) ?_ ?_).symm.subset
    · exact fun x xm=>(mem_union.mp (keep s sm xm)).resolve_left (fun a=>last x a (mem_outN.mp xm).2)
    · rw [size _ hi']; exact quota i hi s sm
  have keep (i) (hi : i < h) : ∀v∈L i,outN D V v⊆L i∪L (i+1) := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro x xm y ym
      obtain ⟨j,le,yj⟩ := step i hi x xm y ym
      by_cases eq : j=i+1
      · exact mem_union_right _ (eq ▸ yj)
      by_cases same : j=i
      · exact mem_union_left _ (same ▸ yj)
      exfalso
      have ji : j < i := by omega
      have arc := (mem_outN.mp ym).2
      have yV := sub j yj
      -- funnel rows
      let G : ℕ → Finset ℕ := fun m => (L m).filter (fun z => Walk D V y z (m - j))
      have reach (m) (jm : j ≤ m) (mi : m < i) :
          ∀ s ∈ L m, Sink D (L m) s → Walk D V s y (i - m + 1) := by
        intro s sm stop
        have tail := EqualLayerTransit.from_sink L free sub i
          (fun k _ ki=>(size k (by omega)).le.trans hq.le)
          (fun k _ ki=>card_pos.mp (by rw [size k (by omega)]; exact hr))
          (fun k _ ki=>sinks (by omega) (by omega) (ih k ki (by omega))) mi sm stop xm
        exact tail.snoc yV arc
      have gdeep (m) (jm : j ≤ m) (mi : m < i) : ∀ z ∈ G m, Deep D (L m) (q - (i - j)) z := by
        intro z zm
        have w := (mem_filter.mp zm).2
        have d := squeeze free (sub m) (by omega) w (reach m jm mi)
        exact d.mono (by omega)
      have grow (m) (jm : j ≤ m) (mi : m + 1 < i) (ne : (G m).Nonempty) :
          (G m).card + (q - (i - j) - 1) ≤ (G (m+1)).card :=
        growth free (sub m) (size m (by omega)) hq.le (by omega) (filter_subset _ _) ne
          (gdeep m jm (by omega)) (fun z zm => quota m (by omega) z (mem_filter.mp zm).1)
          (fun z zm => ih m (by omega) (by omega) z (mem_filter.mp zm).1)
          (fun z zm w wm arc' => mem_filter.mpr ⟨wm, by
            have p := ((mem_filter.mp zm).2).snoc (sub _ wm) arc'
            rwa [show m - j + 1 = m + 1 - j by omega] at p⟩)
      have count : ∀ d, j + d < i → d + 1 ≤ (G (j+d)).card := by
        intro d
        induction d with
        | zero =>
          intro _
          refine card_pos.mpr ⟨y, mem_filter.mpr ⟨yj, ?_⟩⟩
          simpa using (Walk.refl y : Walk D V y y 0)
        | succ d ihd =>
          intro lt
          have prev := ihd (by omega)
          have g := grow (j+d) (by omega) (by omega) (card_pos.mp (by omega))
          rw [show j + (d+1) = j + d + 1 by omega]
          omega
      have last := count (i - 1 - j) (by omega)
      rw [show j + (i - 1 - j) = i - 1 by omega] at last
      have fx : QFree D (L (i-1)) q := free.mono_set (sub _)
      have sz := size (i-1) (by omega)
      have pos : 0 < (G (i-1)).card := by omega
      have bound := deep_card_of (G := G (i-1)) (t := q - (i - j)) fx (sz.le.trans hq.le)
        (filter_subset _ _) (gdeep (i-1) (by omega) (by omega)) (card_pos.mp pos)
      omega
  obtain ⟨s,sm,stop⟩ := exists_sink (free.mono_set (sub (h-1)))
    (card_pos.mp (by rw [size _ (by omega)]; exact hr)) ((size _ (by omega)).le.trans hq.le)
  have bound : outN D V s⊆L h := by
    intro v vm
    have hit := (mem_union.mp (keep (h-1) (by omega) s sm vm)).resolve_left (fun old=>stop v old (mem_outN.mp vm).2)
    rwa [Nat.sub_add_cancel depth] at hit
  exact (quota _ (by omega) s sm).trans (card_le_card bound)

open DotTwoPassShellTransport (layer) in
/-- **Flat roots, persistence form.** `flat_root_false` without `r/2 + h ≤ q`: a root whose first
`h` layers all have width `r` (`h + 1 ≤ q`) has `|ball (h+1)| > r (h+1)`. -/
theorem flat_root_persist {D : CH.Digraph} {V : Finset ℕ} {q r h u : ℕ}
    (free : QFree D V q) (hr : 0 < r) (hq : r < q) (depth : 0 < h)
    (time : h + 1 ≤ q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (flat : ∀ k ≤ h, (ball D V u k).card = r*k + 1)
    (short : (ball D V u (h+1)).card ≤ r*(h+1)) : False := by
  have lay : ∀ k, k < h → (layer D V (k+1) u).card = r := by
    intro k hk
    have e := ShapeClimbRoot.card_ball_succ (D := D) (V := V) (u := u) k
    rw [flat (k+1) (by omega), flat k (by omega)] at e
    have : r*(k+1) = r*k + r := by ring
    omega
  have cap := flat_persist (D := D) (V := V) (q := q) (r := r) (h := h)
    (fun i => layer D V (i+1) u) free hr hq time depth
    (fun i => sdiff_subset.trans ball_subset) lay
    (fun i _ => ShapeClimbRoot.layer_disjoint (by omega))
    (fun i _ v hv => degree v (sdiff_subset.trans ball_subset hv))
    (fun i hi v hv x hx => by
      obtain ⟨j, j1, j2, hj⟩ := ShapeClimbRoot.head_mem free hu (i := i+1) (by omega) (by omega) hv hx
      exact ⟨j - 1, by omega, by rwa [Nat.sub_add_cancel j1]⟩)
  have e := ShapeClimbRoot.card_ball_succ (D := D) (V := V) (u := u) h
  rw [flat h le_rfl] at e
  have : r*(h+1) = r*h + r := by ring
  omega

#print axioms squeeze
#print axioms head_deep
#print axioms deep_card_of
#print axioms growth
#print axioms flat_persist
#print axioms flat_root_persist
end LeanCH.BR.FlatPersist
