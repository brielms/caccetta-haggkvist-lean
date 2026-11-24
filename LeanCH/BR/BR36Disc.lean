import LeanCH.BR.BR36Root

/-!
# Discharging route, part 2: Theorem D, the saturation reduction for every `s ≤ 7`, and `BR(3,6)` (Lean 4.35.0)

Paper source: `checkpoints/boundary_20261111/BR37_attempt_subagent.md`, sections 4 and 7 (Theorem D, Corollary D′).

* `SHyp.no_root` (**Theorem D**). Give each root `u` the witness set `W(u) = H(u)` if `h(u) ≥ 1`, else `K(u)`. Every
  vertex `v` is a witness for `m(v)` roots with `m(v) + in(v) ≤ out(v) + [v root]`, strictly if `v ∈ K(u)` for a
  root `u` with `h(u) ≤ 1` (Lemmas 3-6). Summing, with `Σ in = Σ out`, gives `Σ_u |W(u)| = Σ_v m(v) ≤ #roots`, minus
  one for each strict vertex. So if `K(u) ≠ ∅` at every root with `h(u) ≤ 1`, there is no root.
* `br_of_sat`: for `2 ≤ s ≤ 7` and `BR(3,t)` for `t < s`, it suffices that every saturated boundary graph with
  in-degrees at most `s + 1` (strict cap) has every in-degree at most `s` (same induction on non-arcs as
  `BR36Reduce`).
* `br_le_six` (**Corollary D′**): `BR(3,s)` for `2 ≤ s ≤ 6` from `BR(3,t)`, `t < s`. At a root `K(u) = ∅` would give
  `D[O(u)]` (at most 6 vertices) minimum out-degree 2, against `BR(3,2)` (`ch_subset`).
* `br_six : BoundaryRegular 3 6`.
-/

namespace LeanCH.BR.BR36

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of

/-- The witness set of a root. -/
def Wit (G : CH.Digraph) (s u : Nat) : Finset Nat := if (HS G s u).card = 0 then KS G s u else HS G s u

theorem Wit_sub {G : CH.Digraph} {s u : Nat} : Wit G s u ⊆ VS s := by
  unfold Wit
  split_ifs
  · exact KS_sub.trans (Finset.filter_subset _ _)
  · exact HS_sub.trans (Finset.filter_subset _ _)

/-- Double counting of witness pairs. -/
theorem witness_count (G : CH.Digraph) (s : Nat) (Z : Finset Nat) :
    ∑ u ∈ Z, (Wit G s u).card = ∑ v ∈ VS s, (Z.filter (fun u => v ∈ Wit G s u)).card := by
  classical
  have h1 : ∀ u, (Wit G s u).card = ∑ v ∈ VS s, (if v ∈ Wit G s u then 1 else 0) := by
    intro u
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr Wit_sub]
  rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun v _ => (Finset.card_filter _ _).symm)

namespace SHyp

variable {s : Nat} {G : CH.Digraph} (H : SHyp s G)
include H

/-- **Theorem D.** -/
theorem no_root (hK : ∀ u, IsRoot G s u → (HS G s u).card ≤ 1 → (KS G s u).Nonempty) (u0 : Nat) :
    ¬ IsRoot G s u0 := by
  classical
  intro hu0
  set Z := (VS s).filter (fun u => IsRoot G s u) with hZ
  have memZ : ∀ u, u ∈ Z ↔ IsRoot G s u := fun u => by
    rw [hZ, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_VS.mpr h.1, h⟩⟩
  have hZV : Z ⊆ VS s := Finset.filter_subset _ _
  -- the claim at one vertex
  have claim : ∀ v ∈ VS s, (Z.filter (fun u => v ∈ Wit G s u)).card + ic G (VS s) v +
      (if ∃ u ∈ Z, (HS G s u).card ≤ 1 ∧ v ∈ KS G s u then 1 else 0) ≤
        oc G (VS s) v + (if v ∈ Z then 1 else 0) := by
    intro v hv
    have hvn := mem_VS.mp hv
    set RH := Z.filter (fun u => v ∈ HS G s u) with hRH
    set RK := Z.filter (fun u => (HS G s u).card = 0 ∧ v ∈ KS G s u) with hRK
    have hm : (Z.filter (fun u => v ∈ Wit G s u)).card = RH.card + RK.card := by
      have e1 : Z.filter (fun u => v ∈ Wit G s u) =
          Z.filter (fun u => v ∈ HS G s u ∨ ((HS G s u).card = 0 ∧ v ∈ KS G s u)) := by
        apply Finset.filter_congr
        intro u _
        unfold Wit
        by_cases h : (HS G s u).card = 0
        · rw [if_pos h, Finset.card_eq_zero.mp h]
          simp
        · rw [if_neg h]
          simp [h]
      rw [e1, Finset.filter_or, Finset.card_union_of_disjoint]
      rw [Finset.disjoint_filter]
      intro u _ h1 h2
      rw [Finset.card_eq_zero.mp h2.1] at h1
      exact Finset.notMem_empty v h1
    have hRK1 : RK.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      by_contra hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      exact H.lemma6 ((memZ a).mp ha'.1) ((memZ b).mp hb'.1) hab hb'.2.1 ha'.2.2 hb'.2.2
    have fRH : RH.card = 0 ∨ (ic G (VS s) v + RH.card ≤ oc G (VS s) v ∧
        RH.card + 2 * s + 1 ≤ 2 * oc G (VS s) v) := by
      by_cases h0 : RH.card = 0
      · exact Or.inl h0
      · right
        exact H.lemma5 hvn (Finset.card_pos.mp (Nat.pos_of_ne_zero h0)) (fun u hu => by
          obtain ⟨huZ, hvu⟩ := Finset.mem_filter.mp hu
          exact ⟨(memZ u).mp huZ, hvu⟩)
    have fRK : RK.card = 0 ∨ (ic G (VS s) v + oc G (VS s) v + 1 ≤ 2 * s ∧
        ic G (VS s) v + 2 ≤ oc G (VS s) v) := by
      by_cases h0 : RK.card = 0
      · exact Or.inl h0
      · right
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        have hu' := Finset.mem_filter.mp hu
        have k1 := H.K1 ((memZ u).mp hu'.1) hu'.2.2
        have k2 := H.K2 ((memZ u).mp hu'.1) hu'.2.2
        rw [hu'.2.1] at k1 k2
        exact ⟨by omega, by omega⟩
    have fstr : (∃ u ∈ Z, (HS G s u).card ≤ 1 ∧ v ∈ KS G s u) →
        ∃ h, h ≤ 1 ∧ ic G (VS s) v + oc G (VS s) v + 1 ≤ 2 * s + h ∧ ic G (VS s) v + 2 ≤ oc G (VS s) v + h ∧
          (h = 0 → 1 ≤ RK.card) := by
      rintro ⟨u, huZ, hH1, hvK⟩
      refine ⟨(HS G s u).card, hH1, H.K1 ((memZ u).mp huZ) hvK, H.K2 ((memZ u).mp huZ) hvK, fun h0 => ?_⟩
      exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨huZ, h0, hvK⟩⟩
    have hcap := H.cap v hvn
    have hout := H.out hvn
    have hroot : v ∈ Z ↔ ic G (VS s) v = s + 1 ∧ oc G (VS s) v = s := by
      rw [memZ]
      exact ⟨fun h => h.2, fun h => ⟨hvn, h⟩⟩
    rw [hm]
    by_cases hs : ∃ u ∈ Z, (HS G s u).card ≤ 1 ∧ v ∈ KS G s u
    · obtain ⟨h, hh1, hh2, hh3, hh4⟩ := fstr hs
      rw [if_pos hs]
      by_cases hvZ : v ∈ Z
      · rw [if_pos hvZ]
        have := hroot.mp hvZ
        omega
      · rw [if_neg hvZ]
        have : ¬ (ic G (VS s) v = s + 1 ∧ oc G (VS s) v = s) := fun h => hvZ (hroot.mpr h)
        rcases fRH with h1 | h1 <;> rcases fRK with h2 | h2 <;>
          · have : h = 0 ∨ h = 1 := by omega
            rcases this with rfl | rfl <;> omega
    · rw [if_neg hs]
      by_cases hvZ : v ∈ Z
      · rw [if_pos hvZ]
        have := hroot.mp hvZ
        omega
      · rw [if_neg hvZ]
        have : ¬ (ic G (VS s) v = s + 1 ∧ oc G (VS s) v = s) := fun h => hvZ (hroot.mpr h)
        omega
  -- summing the claim
  have S := Finset.sum_le_sum claim
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at S
  have hsum : ∑ v ∈ VS s, oc G (VS s) v = ∑ v ∈ VS s, ic G (VS s) v :=
    Compose.ThinRigid.sum_out_eq_sum_in G (VS s)
  have hZc : ∑ v ∈ VS s, (if v ∈ Z then 1 else 0) = Z.card := by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hZV]
  rw [hZc, ← witness_count G s Z] at S
  have hW1 : ∀ u ∈ Z, 1 ≤ (Wit G s u).card := by
    intro u hu
    have hr := (memZ u).mp hu
    unfold Wit
    split_ifs with h
    · exact Finset.card_pos.mpr (hK u hr (by omega))
    · omega
  have hlow := card_mul_le_sum hW1
  rw [mul_one] at hlow
  have hu0Z : u0 ∈ Z := (memZ u0).mpr hu0
  by_cases h2 : 2 ≤ (HS G s u0).card
  · have hlt : 1 + 1 ≤ (Wit G s u0).card := by
      unfold Wit; rw [if_neg (by omega)]; exact h2
    have := sum_add_one_le hW1 hu0Z hlt
    rw [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  · obtain ⟨x, hx⟩ := hK u0 hu0 (by omega)
    have hxV : x ∈ VS s := (KS_sub.trans (Finset.filter_subset _ _)) hx
    have hstr := Finset.single_le_sum (f := fun v => if ∃ u ∈ Z, (HS G s u).card ≤ 1 ∧ v ∈ KS G s u then 1 else 0)
      (fun _ _ => Nat.zero_le _) hxV
    rw [if_pos ⟨u0, hu0Z, by omega, hx⟩] at hstr
    omega

end SHyp

/-- In-degree at most `s` everywhere and minimum out-degree `s` force in-degree exactly `s`. -/
theorem reg_of_le_s {s : Nat} {G : CH.Digraph} (deg : CH.MinOutdegreeAtLeast G (3 * s + 1) s)
    (hle : ∀ v, v < 3 * s + 1 → ic G (VS s) v ≤ s) : ∀ v, v < 3 * s + 1 → ic G (VS s) v = s := by
  have hle' : ∀ v ∈ VS s, ic G (VS s) v ≤ s := fun v hv => hle v (mem_VS.mp hv)
  have hge : ∑ _v ∈ VS s, s ≤ ∑ v ∈ VS s, ic G (VS s) v :=
    calc ∑ _v ∈ VS s, s
        ≤ ∑ x ∈ VS s, oc G (VS s) x := Finset.sum_le_sum (fun x hx => out_card deg (mem_VS.mp hx))
      _ = ∑ v ∈ VS s, ic G (VS s) v := Compose.ThinRigid.sum_out_eq_sum_in G _
  have heq := le_antisymm (Finset.sum_le_sum hle') hge
  have each := (Finset.sum_eq_sum_iff_of_le hle').mp heq
  intro v hv
  exact each v (mem_VS.mpr hv)

/-- **Reduction to saturated graphs**, for `2 ≤ s ≤ 7`. -/
theorem br_of_sat {s : Nat} (hs : 2 ≤ s) (hs7 : s ≤ 7) (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t)
    (main : ∀ G : CH.Digraph, SHyp s G →
      (∀ v, v < 3 * s + 1 → s ≤ ic G (VS s) v →
        3 * (ic G (VS s) v - s) + 2 * (oc G (VS s) v - s) + 2 ≤ s) →
      ∀ v, v < 3 * s + 1 → ic G (VS s) v ≤ s) :
    BoundaryRegular 3 s := by
  classical
  suffices key : ∀ (k : Nat) (G : CH.Digraph), LeanCH.BR.Reduce.miss G (3 * s + 1) = k →
      CH.Loopless G (3 * s + 1) → CH.MinOutdegreeAtLeast G (3 * s + 1) s →
      ¬ CH.HasDirectedCycleAtMost G (3 * s + 1) 3 → ∀ v, v < 3 * s + 1 → ic G (VS s) v = s by
    intro G loopless deg noShort v hv
    exact key _ G rfl loopless deg noShort v hv
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro G hk loopless deg noShort
  have cap : ∀ v, v < 3 * s + 1 → s ≤ ic G (VS s) v →
      3 * (ic G (VS s) v - s) + 2 * (oc G (VS s) v - s) + 2 ≤ s :=
    fun v hv hin => LeanCH.BR.StrictCap.strict_cap (s := s) hs brs loopless deg noShort hv hin
  by_cases hsat : ∀ a b, a < 3 * s + 1 → b < 3 * s + 1 → a ≠ b → G a b = false → G b a = false →
      ∃ z, z < 3 * s + 1 ∧ G a z = true ∧ G z b = true
  · have H : SHyp s G :=
      { loopless := loopless
        deg := deg
        noShort := noShort
        cap := fun v hv => by
          by_contra h
          have := cap v hv (by omega)
          omega
        sat := hsat }
    exact reg_of_le_s deg (main G H cap)
  · push Not at hsat
    obtain ⟨a, b, ha, hb, hab, gab, gba, hno⟩ := hsat
    have hno' : ∀ z, z < 3 * s + 1 → G a z = true → G z b = false := fun z hz h => by simpa using hno z hz h
    set G' := LeanCH.BR.Reduce.addArc G b a with hG'
    have arc : ∀ x y, G' x y = true → (x = b ∧ y = a) ∨ G x y = true := by
      intro x y h
      simp only [hG', LeanCH.BR.Reduce.addArc] at h
      split_ifs at h with hxy
      · exact Or.inl hxy
      · exact Or.inr h
    have N2 := fun {x y : Nat} => @no2 G (3 * s + 1) loopless noShort x y
    have N3 := fun {x y z : Nat} => @no3 G (3 * s + 1) loopless noShort x y z
    have loop' : CH.Loopless G' (3 * s + 1) := by
      intro w hw
      have : ¬ (w = b ∧ w = a) := fun h => hab (h.2.symm.trans h.1)
      simp only [hG', LeanCH.BR.Reduce.addArc, this]; exact loopless w hw
    have short' : ¬ CH.HasDirectedCycleAtMost G' (3 * s + 1) 3 := by
      apply noShort_of
      · intro x y hx hy e1 e2
        rcases arc x y e1 with ⟨h1, h2⟩ | e1
        · rw [h1, h2] at e2
          rcases arc a b e2 with ⟨h, _⟩ | e2
          · exact hab h
          · rw [gab] at e2; exact Bool.false_ne_true e2
        · rcases arc y x e2 with ⟨h1, h2⟩ | e2
          · rw [h1, h2, gab] at e1; exact Bool.false_ne_true e1
          · exact N2 hx hy e1 e2
      · intro x y z hx hy hz e1 e2 e3
        rcases arc x y e1 with ⟨h1, h2⟩ | e1
        · rw [h2] at e2
          rw [h1] at e3
          have e2' : G a z = true := by
            rcases arc a z e2 with ⟨h, _⟩ | e2
            · exact absurd h hab
            · exact e2
          have e3' : G z b = true := by
            rcases arc z b e3 with ⟨_, h⟩ | e3
            · exact absurd h.symm hab
            · exact e3
          rw [hno' z hz e2'] at e3'; exact Bool.false_ne_true e3'
        · rcases arc y z e2 with ⟨h1, h2⟩ | e2
          · rw [h2] at e3
            rw [h1] at e1
            have e3' : G a x = true := by
              rcases arc a x e3 with ⟨h, _⟩ | e3
              · exact absurd h hab
              · exact e3
            rw [hno' x hx e3'] at e1; exact Bool.false_ne_true e1
          · rcases arc z x e3 with ⟨h1, h2⟩ | e3
            · rw [h2] at e1
              rw [h1] at e2
              rw [hno' y hy e1] at e2; exact Bool.false_ne_true e2
            · exact N3 hx hy hz e1 e2 e3
    have deg' := minOut_mono (LeanCH.BR.Reduce.addArc_ge G b a) deg
    have hlt := LeanCH.BR.Reduce.miss_lt hb ha (Ne.symm hab) gba
    have reg' := IH _ (hk ▸ hlt) G' rfl loop' deg' short'
    apply reg_of_le_s deg
    intro v hv
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (reg' v hv))
    intro w hw
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨h1, LeanCH.BR.Reduce.addArc_ge G b a w v h2⟩

/-- `K(u) ≠ ∅` at a root as soon as `BR(3,2)` excludes `D[O(u)]` (`s ≤ 6`). -/
theorem SHyp.K_nonempty {s : Nat} {G : CH.Digraph} (H : SHyp s G) (hs2 : 2 ≤ s) (hs6 : s ≤ 6) {u : Nat}
    (hr : IsRoot G s u) : (KS G s u).Nonempty := by
  classical
  by_contra hK
  rw [Finset.not_nonempty_iff_eq_empty] at hK
  have hM := H.root_M hr
  apply ch_subset (q := 3) (c := 2) (S := OO G s u) (by norm_num) LeanCH.BR.SmallBR.br_two H.subO
    (Finset.card_pos.mp (by rw [card_OO, hr.2.2]; omega)) (by rw [card_OO, hr.2.2]; omega) H.loopless
    H.noShort
  intro x hx
  have hxK : x ∉ KS G s u := by rw [hK]; exact Finset.notMem_empty x
  have : ∃ m ∈ MM G s u, G x m = false := by
    by_contra hcon
    push Not at hcon
    exact hxK (Finset.mem_filter.mpr ⟨hx, fun m hm => by simpa using hcon m hm⟩)
  obtain ⟨m, hm, hxm⟩ := this
  have h1 := H.out (H.ltO hx)
  rw [H.outO hr.1 hx] at h1
  have h2 : oc G (MM G s u) x ≤ (MM G s u).card - 1 := by
    rw [← oc_erase_eq (G := G) (A := MM G s u) hxm, ← Finset.card_erase_of_mem hm]
    exact oc_le _ x
  omega

/-- **Corollary D′.** `BR(3,s)` for `2 ≤ s ≤ 6`, from `BR(3,t)` for `t < s`. -/
theorem br_le_six {s : Nat} (hs2 : 2 ≤ s) (hs6 : s ≤ 6) (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t) :
    BoundaryRegular 3 s := by
  apply br_of_sat hs2 (by omega) brs
  intro G H cap v hv
  by_contra hgt
  have h1 := H.cap v hv
  have h2 := cap v hv (by omega)
  have h3 := H.out hv
  exact H.no_root (fun u hr _ => H.K_nonempty hs2 hs6 hr) v ⟨hv, by omega, by omega⟩

/-- **`BR(3,6)`.** Every loopless digraph on 19 labels with minimum out-degree 6 and no directed cycle of length at
most 3 has every in-degree exactly 6. -/
theorem br_six : BoundaryRegular 3 6 := br_le_six (by norm_num) (le_refl _) brs6

end LeanCH.BR.BR36
