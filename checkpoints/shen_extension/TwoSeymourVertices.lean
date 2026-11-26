import checkpoints.shen_extension.TwoSeymourDeficit
import checkpoints.shen_extension.TwoSeymourEndgame

/-!
Every nonempty finite sinkless oriented graph has two distinct vertices whose exact second
out-neighbourhood is at least as large as the first.

Proof (after M. Kang, October 2026, from the vendored one-vertex theorem and pruning
theorem): a counterexample with the fewest vertices and then the fewest arcs has a unique
good vertex `g`, with exactly one successor `h`, and no proper nonempty out-closed set.
Every source set avoiding `g` has a strict subset deficit (`deficit_avoiding`). After
deleting `g` the deficits are weak, and strict away from `h` (`erase_deficit`), and the
deleted graph has positive in-degrees. `endgame` excludes such a graph.
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood

theorem card_sdiff_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    (A B : Finset α) : (A.map f \ B.map f).card = (A \ B).card := by
  rw [← Finset.card_map f]
  congr 1
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_map]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hnb⟩
    exact ⟨a, ⟨ha, fun hb => hnb ⟨a, hb, rfl⟩⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hnb⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, fun ⟨b, hb, hbe⟩ => hnb (f.injective hbe ▸ hb)⟩

section Core

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph with `g` deleted. -/
def delRel (r : V → V → Prop) (g : V) : {v : V // v ≠ g} → {v : V // v ≠ g} → Prop :=
  fun x y => r x.1 y.1

/-- The inclusion of the deleted graph. -/
def delEmb (g : V) : {v : V // v ≠ g} ↪ V := Function.Embedding.subtype _

theorem map_image_del (r : V → V → Prop) (g : V) (S : Finset {v : V // v ≠ g}) :
    (image (delRel r g) S).map (delEmb g) = (image r (S.map (delEmb g))).erase g := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨y₀, hy₀, hyy⟩ := Finset.mem_map.mp hy
    obtain ⟨x₀, hx₀, hxy⟩ := mem_image.mp hy₀
    have hyv : y₀.1 = y := hyy
    rw [← hyv]
    refine Finset.mem_erase.mpr ⟨y₀.2, mem_image.mpr ⟨x₀.1, ?_, hxy⟩⟩
    exact Finset.mem_map.mpr ⟨x₀, hx₀, rfl⟩
  · intro hy
    obtain ⟨hyg, hyim⟩ := Finset.mem_erase.mp hy
    obtain ⟨x, hx, hxy⟩ := mem_image.mp hyim
    obtain ⟨x₀, hx₀, hxx⟩ := Finset.mem_map.mp hx
    have hxv : x₀.1 = x := hxx
    rw [← hxv] at hxy
    exact Finset.mem_map.mpr ⟨⟨y, hyg⟩, mem_image.mpr ⟨x₀, hx₀, hxy⟩, rfl⟩

/-- A graph with a unique good vertex that is minimal in arcs and has no proper nonempty
out-closed set does not exist. -/
theorem core (r : V → V → Prop) (hr : IsOriented r) (hsl : ∀ v, ∃ w, r v w) (g : V)
    (hbad : ∀ v, v ≠ g → (secondNeighbors r v).card < (firstNeighbors r v).card)
    (hmin : ∀ s : V → V → Prop, IsOriented s → (arcSet s).card < (arcSet r).card →
      (∀ v, ∃ w, s v w) → ∃ u v, u ≠ v ∧ GoodVertex s u ∧ GoodVertex s v)
    (hclosed : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → image r S ⊆ S → False) :
    False := by
  classical
  obtain ⟨h, hgh⟩ := hsl g
  -- `g` has exactly one successor
  have hone : ∀ w, r g w → w = h := by
    intro w hgw
    by_contra hne
    let s : V → V → Prop := fun x y => r x y ∧ ¬ (x = g ∧ y = w)
    have hs : IsOriented s := hr.mono (fun _ _ h => h.1)
    have hsl' : ∀ v, ∃ w', s v w' := by
      intro v
      by_cases hv : v = g
      · refine ⟨h, ?_, fun hc => hne hc.2.symm⟩
        rw [hv]
        exact hgh
      · obtain ⟨w', hw'⟩ := hsl v
        exact ⟨w', hw', fun hc => hv hc.1⟩
    have hlt : (arcSet s).card < (arcSet r).card := by
      apply Finset.card_lt_card
      refine ⟨?_, ?_⟩
      · apply arcSet_mono
        intro x y hxy
        exact hxy.1
      · intro hrev
        have hmem : (g, w) ∈ arcSet r := mem_arcSet.mpr hgw
        have hsgw : s g w := mem_arcSet.mp (hrev hmem)
        exact hsgw.2 ⟨rfl, rfl⟩
    obtain ⟨u, v, huv, hu, hv⟩ := hmin s hs hlt hsl'
    have key : ∀ x, x ≠ g → GoodVertex s x → False := by
      intro x hx hgood
      have hfirst : firstNeighbors s x = firstNeighbors r x := by
        ext y
        rw [mem_firstNeighbors, mem_firstNeighbors]
        exact ⟨fun hxy => hxy.1, fun hxy => ⟨hxy, fun hc => hx hc.1⟩⟩
      have hsecond : secondNeighbors s x ⊆ secondNeighbors r x := by
        intro y hy
        obtain ⟨hyx, hnot, z, hxz, hzy⟩ := mem_secondNeighbors.mp hy
        exact mem_secondNeighbors.mpr
          ⟨hyx, fun hxy => hnot ⟨hxy, fun hc => hx hc.1⟩, z, hxz.1, hzy.1⟩
      have hb := hbad x hx
      have hc := Finset.card_le_card hsecond
      unfold GoodVertex at hgood
      rw [hfirst] at hgood
      omega
    by_cases hug : u = g
    · exact key v (fun hvg => huv (hug.trans hvg.symm)) hv
    · exact key u hug hu
  have hhg : h ≠ g := by
    intro heq
    rw [heq] at hgh
    exact hr.loopless g hgh
  -- strict deficits away from `g`
  have hD : ∀ S : Finset V, S.Nonempty → g ∉ S →
      (image r (image r S) \ image r S).card < (image r S \ S).card := by
    intro S hS hgS
    apply deficit_avoiding r hr g ⟨h, hgh⟩ hbad hmin S hgS
    by_contra hE
    apply hclosed S hS
    · intro hSu
      apply hgS
      rw [hSu]
      exact Finset.mem_univ g
    · intro x hx
      by_contra hxS
      exact hE ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxS⟩⟩
  -- positive in-degrees after deleting `g`
  have hpos : PositiveIndegree (delRel r g) := by
    intro v
    by_contra hnone
    have hno : ∀ u, u ≠ g → ¬ r u v.1 := by
      intro u hu hc
      exact hnone ⟨⟨u, hu⟩, hc⟩
    by_cases hvh : v.1 = h
    · obtain ⟨w, hhw⟩ := hsl h
      have hwh : w ≠ h := by
        intro heq
        rw [heq] at hhw
        exact hr.loopless h hhw
      have hwg : w ≠ g := by
        intro heq
        rw [heq] at hhw
        exact hr.asymmetric hgh hhw
      let S : Finset V := (Finset.univ.erase g).erase h
      have hS : S.Nonempty :=
        ⟨w, Finset.mem_erase.mpr ⟨hwh, Finset.mem_erase.mpr ⟨hwg, Finset.mem_univ w⟩⟩⟩
      have hgS : g ∉ S := by
        intro hc
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1 rfl
      have hd := hD S hS hgS
      have hhN : h ∉ image r S := by
        intro hc
        obtain ⟨u, hu, huh⟩ := mem_image.mp hc
        have hug : u ≠ g := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
        apply hno u hug
        rw [hvh]
        exact huh
      have hEsub : image r S \ S ⊆ {g} := by
        intro x hx
        obtain ⟨hxim, hxS⟩ := Finset.mem_sdiff.mp hx
        rw [Finset.mem_singleton]
        by_contra hxg
        have hxh : x ≠ h := by
          intro heq
          rw [heq] at hxim
          exact hhN hxim
        exact hxS (Finset.mem_erase.mpr
          ⟨hxh, Finset.mem_erase.mpr ⟨hxg, Finset.mem_univ x⟩⟩)
      have hEcard := Finset.card_le_card hEsub
      rw [Finset.card_singleton] at hEcard
      have hEne : (image r S \ S).Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨x, hx⟩ := hEne
      have hxg : x = g := Finset.mem_singleton.mp (hEsub hx)
      have hgN : g ∈ image r S := by
        rw [← hxg]
        exact (Finset.mem_sdiff.mp hx).1
      have hhD : h ∈ image r (image r S) \ image r S :=
        Finset.mem_sdiff.mpr ⟨mem_image.mpr ⟨g, hgN, hgh⟩, hhN⟩
      have hDpos := Finset.card_pos.mpr ⟨h, hhD⟩
      omega
    · let S : Finset V := Finset.univ.erase v.1
      apply hclosed S
      · exact ⟨g, Finset.mem_erase.mpr ⟨fun heq => v.2 heq.symm, Finset.mem_univ g⟩⟩
      · intro hSu
        have hmem : v.1 ∈ S := by
          rw [hSu]
          exact Finset.mem_univ _
        exact (Finset.mem_erase.mp hmem).1 rfl
      · intro x hx
        obtain ⟨u, hu, hux⟩ := mem_image.mp hx
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
        intro hxv
        rw [hxv] at hux
        by_cases hug : u = g
        · rw [hug] at hux
          exact hvh (hone v.1 hux)
        · exact hno u hug hux
  -- weak deficits, strict away from `h`, in the deleted graph
  have htransfer : ∀ S₀ : Finset {v : V // v ≠ g}, S₀.Nonempty →
      ((image (delRel r g) (image (delRel r g) S₀) \ image (delRel r g) S₀).card ≤
        (image (delRel r g) S₀ \ S₀).card) ∧
      ((⟨h, hhg⟩ : {v : V // v ≠ g}) ∉ image (delRel r g) S₀ →
        (⟨h, hhg⟩ : {v : V // v ≠ g}) ∉ image (delRel r g) (image (delRel r g) S₀) →
        (image (delRel r g) (image (delRel r g) S₀) \ image (delRel r g) S₀).card <
          (image (delRel r g) S₀ \ S₀).card) := by
    intro S₀ hS₀
    have hgS : g ∉ S₀.map (delEmb g) := by
      intro hc
      obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hc
      exact x.2 hx
    have hSne : (S₀.map (delEmb g)).Nonempty := by
      obtain ⟨x, hx⟩ := hS₀
      exact ⟨delEmb g x, Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
    have hd := hD (S₀.map (delEmb g)) hSne hgS
    obtain ⟨hw, hst⟩ := erase_deficit r hr g h hgh (S₀.map (delEmb g)) hd hgS
    have e1 := map_image_del r g S₀
    have e2 : (image (delRel r g) (image (delRel r g) S₀)).map (delEmb g) =
        (image r ((image r (S₀.map (delEmb g))).erase g)).erase g := by
      rw [map_image_del, e1]
    have c1 : (image (delRel r g) (image (delRel r g) S₀) \ image (delRel r g) S₀).card =
        ((image r ((image r (S₀.map (delEmb g))).erase g)).erase g \
          (image r (S₀.map (delEmb g))).erase g).card := by
      rw [← e2, ← e1]
      exact (card_sdiff_map (delEmb g) _ _).symm
    have c2 : (image (delRel r g) S₀ \ S₀).card =
        ((image r (S₀.map (delEmb g))).erase g \ S₀.map (delEmb g)).card := by
      rw [← e1]
      exact (card_sdiff_map (delEmb g) _ _).symm
    rw [c1, c2]
    refine ⟨hw, fun h1 h2 => hst ?_ ?_⟩
    · rw [← e1]
      intro hc
      obtain ⟨y, hy, hyh⟩ := Finset.mem_map.mp hc
      have hyeq : y = ⟨h, hhg⟩ := Subtype.ext hyh
      rw [hyeq] at hy
      exact h1 hy
    · rw [← e2]
      intro hc
      obtain ⟨y, hy, hyh⟩ := Finset.mem_map.mp hc
      have hyeq : y = ⟨h, hhg⟩ := Subtype.ext hyh
      rw [hyeq] at hy
      exact h2 hy
  have : Nonempty {v : V // v ≠ g} := ⟨⟨h, hhg⟩⟩
  exact endgame (r := delRel r g)
    ⟨fun x => hr.loopless x.1, fun hxy hyx => hr.asymmetric hxy hyx⟩ hpos
    (fun S hS _ => (htransfer S hS).1) ⟨h, hhg⟩
    (fun S hS _ h1 h2 => (htransfer S hS).2 h1 h2)

end Core

/-- The two-vertex theorem on `Fin n`, by induction on the order and then on the arcs. -/
theorem two_good_fin : ∀ n : ℕ, 0 < n → ∀ r : Fin n → Fin n → Prop, IsOriented r →
    (∀ v, ∃ w, r v w) → ∃ u v, u ≠ v ∧ GoodVertex r u ∧ GoodVertex r v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro hn r
    generalize ha : (arcSet r).card = a
    induction a using Nat.strong_induction_on generalizing r with
    | _ a iha =>
      intro hr hsl
      by_contra hno
      have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      obtain ⟨g, hg⟩ := exists_goodVertex r hr
      have hbad : ∀ v, v ≠ g →
          (secondNeighbors r v).card < (firstNeighbors r v).card := by
        intro v hvg
        by_contra hnb
        exact hno ⟨v, g, hvg, Nat.le_of_not_lt hnb, hg⟩
      apply core r hr hsl g hbad
      · intro s hs hlt hsl'
        exact iha (arcSet s).card (by omega) s rfl hs hsl'
      · intro S hS hSu hcl
        have hcardlt : Fintype.card ↥S < n := by
          rw [Fintype.card_coe]
          have hlt := (Finset.card_lt_iff_ne_univ S).mpr hSu
          simpa using hlt
        have hcardpos : 0 < Fintype.card ↥S := by
          rw [Fintype.card_coe]
          exact Finset.card_pos.mpr hS
        let e := Fintype.equivFin ↥S
        obtain ⟨u, v, huv, hu, hv⟩ := ihn (Fintype.card ↥S) hcardlt hcardpos
          (reindex e (induced r S)) (isOriented_reindex e (isOriented_induced hr S)) (by
            intro w
            obtain ⟨y, hy⟩ := hsl (e.symm w).1
            have hyS : y ∈ S := hcl (mem_image.mpr ⟨(e.symm w).1, (e.symm w).2, hy⟩)
            refine ⟨e ⟨y, hyS⟩, ?_⟩
            show r (e.symm w).1 (e.symm (e ⟨y, hyS⟩)).1
            rw [Equiv.symm_apply_apply]
            exact hy)
        have tr : ∀ w, GoodVertex (reindex e (induced r S)) w →
            GoodVertex r (e.symm w).1 := by
          intro w hw
          unfold GoodVertex at hw ⊢
          rw [card_firstNeighbors_reindex, card_secondNeighbors_reindex,
            card_firstNeighbors_induced hcl, card_secondNeighbors_induced hcl] at hw
          exact hw
        apply hno
        refine ⟨(e.symm u).1, (e.symm v).1, ?_, tr u hu, tr v hv⟩
        intro heq
        exact huv (e.symm.injective (Subtype.ext heq))

/-- **Two good vertices.** Every nonempty finite oriented graph without a sink has two
distinct vertices whose exact second out-neighbourhood is at least as large as the first. -/
theorem exists_two_goodVertices {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (r : V → V → Prop) (hr : IsOriented r) (hsl : ∀ v, ∃ w, r v w) :
    ∃ u v, u ≠ v ∧ GoodVertex r u ∧ GoodVertex r v := by
  classical
  let e := Fintype.equivFin V
  obtain ⟨u, v, huv, hu, hv⟩ := two_good_fin (Fintype.card V) Fintype.card_pos
    (reindex e r) (isOriented_reindex e hr) (by
      intro w
      obtain ⟨y, hy⟩ := hsl (e.symm w)
      refine ⟨e y, ?_⟩
      show r (e.symm w) (e.symm (e y))
      rw [Equiv.symm_apply_apply]
      exact hy)
  refine ⟨e.symm u, e.symm v, fun heq => huv (e.symm.injective heq), ?_, ?_⟩
  · unfold GoodVertex at hu ⊢
    rw [card_firstNeighbors_reindex, card_secondNeighbors_reindex] at hu
    exact hu
  · unfold GoodVertex at hv ⊢
    rw [card_firstNeighbors_reindex, card_secondNeighbors_reindex] at hv
    exact hv

end LeanCH.BR.TwoSeymour

#print axioms LeanCH.BR.TwoSeymour.exists_two_goodVertices
