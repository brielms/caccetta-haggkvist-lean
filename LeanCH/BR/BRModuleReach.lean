import LeanCH.BR.BRModuleCover

/-! Common exterior heads force growth at a parent; small local cycles cannot be modules. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

/-- Transport the set-ball beyond a complete first-layer block, keeping the root
and that block disjoint from the transported set. No module existence is assumed. -/
theorem common_heads_parent_ball {D : CH.Digraph} {V M Y : Finset ℕ} {u q k : ℕ}
    (hq : 2 ≤ q) (hk : k ≤ q - 2) (hf : QFree D V q) (hu : u ∈ V)
    (hMX : M ⊆ outN D V u) (hMn : M.Nonempty) (hYV : Y ⊆ V)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true) :
    M.card + (ballSet D V Y k).card + 1 ≤ (ball D V u (k + 2)).card := by
  classical
  have hMV : M ⊆ V := hMX.trans outN_subset
  obtain ⟨m, hm⟩ := hMn
  have hum := (mem_outN.mp (hMX hm)).2
  have hsep := lemmaM_a hq hf hMV hYV hhead
  have hd : Disjoint M (ballSet D V Y k) :=
    hsep.1.mono_right (ballSet_mono hk)
  have hun : u ∉ M ∪ ballSet D V Y k := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact loopfree hf (by omega) hu (mem_outN.mp (hMX h)).2
    · exact hsep.2 u (ballSet_mono hk h) m hm hum
  have hsub : insert u (M ∪ ballSet D V Y k) ⊆ ball D V u (k + 2) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact self_mem_ball hu
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact ball_mono_radius (by omega) (ball_of_adj (hMV hz) (mem_outN.mp (hMX hz)).2)
      · obtain ⟨y, hy, hzy⟩ := mem_ballSet.mp hz
        have hy2 := ball_step (ball_of_adj (hMV hm) hum) (hYV hy) (hhead m hm y hy)
        simpa only [Nat.add_comm 2 k] using ball_trans hy2 hzy
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hun, Finset.card_union_of_disjoint hd] at hc
  exact hc

/-- Six first neighbors with five common heads already force B4>=24. -/
theorem six_common_heads_ball_four {D : CH.Digraph} {V M Y : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hMX : M ⊆ outN D V u) (hM : M.card = 6) (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true) :
    24 ≤ (ball D V u 4).card := by
  have hc := common_heads_parent_ball (k := 2) (by decide) (by decide) hf hu hMX
    (Finset.card_pos.mp (by omega)) hYV hhead
  have hb := card_ballSet_two_ge_seventeen hf hsat hV hm hYV hY
  change M.card + (ballSet D V Y 2).card + 1 ≤ (ball D V u 4).card at hc
  omega

theorem TightSixModule.parent_ball_four_ge_twenty_four {D : CH.Digraph}
    {V M : Finset ℕ} (h : TightSixModule D V M)
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) {u : ℕ}
    (hu : u ∈ moduleParents D V M) : 24 ≤ (ball D V u 4).card := by
  obtain ⟨huVM, x, hx, hux⟩ := Finset.mem_filter.mp hu
  obtain ⟨huV, huM⟩ := Finset.mem_sdiff.mp huVM
  obtain ⟨Y, hYV, hY, hhead, hout⟩ := h.exterior
  have hMX : M ⊆ outN D V u := by
    intro y hy
    exact mem_outN.mpr ⟨h.subset hy, module_parent_uniform
      (by decide : 5 + 1 = 6) (by decide) hf hsat h.subset hYV hY hhead hout h.cycle
      u huV huM x hx y hy hux⟩
  exact six_common_heads_ball_four hf hsat huV hV hm hMX h.card hYV hY hhead

theorem TightSixModule.parent_in_le_seven {D : CH.Digraph}
    {V M : Finset ℕ} (h : TightSixModule D V M)
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) {u : ℕ}
    (hu : u ∈ moduleParents D V M) : (inN D V u).card ≤ 7 := by
  have hb := h.parent_ball_four_ge_twenty_four hf hsat hV hm hu
  have huV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).1
  have hc := card_inN_of_satQ (by decide : 1 ≤ 5) hf hsat huV
  change (inN D V u).card + (ball D V u 4).card = V.card at hc
  omega

/-- In the surviving B4<=23 profiles, the local six-cycle cannot be a tight module. -/
theorem no_local_tight_six_small_ball {D : CH.Digraph} {V M : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23) (hMsub : M ⊆ (ball D V u 3).erase u) :
    ¬ TightSixModule D V M := by
  intro h
  obtain ⟨Y, hYV, hY, hhead, hout⟩ := h.exterior
  have hpos := tight_six_small_profile_position hf hsat hu hV hm hp hsmall hMsub
    h.card hYV hY hhead hout h.cycle
  have hb := six_common_heads_ball_four hf hsat hu hV hm hpos.1 h.card hYV hY hhead
  omega

/-- Uniform exterior adjacency and exact ambient degree reconstruct the module
data. This is uniform in q and does not assert that cycles have uniform exteriors. -/
theorem tight_cycle_module_of_uniform_exterior {D : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hout : ∀ x ∈ M, (outN D V x).card = q + 1)
    (huniform : ∀ x ∈ M, ∀ y ∈ M, ∀ z ∈ V \ M, D x z = D y z) :
    TightCycleModule q D V M := by
  classical
  obtain ⟨x, hx⟩ : M.Nonempty := Finset.card_pos.mp (by omega)
  let Y := outN D (V \ M) x
  have hpart : M ∪ (V \ M) = V := Finset.union_sdiff_of_subset hMV
  have hc := card_outN_union (D := D) (show Disjoint M (V \ M) from Finset.disjoint_sdiff) x
  rw [hpart, hout x hx, hcyc x hx] at hc
  have hY : Y.card = q := by change (outN D (V \ M) x).card = q; omega
  refine ⟨hMV, hM, hcyc, Y, outN_subset.trans Finset.sdiff_subset, hY, ?_, hout⟩
  intro y hy z hz
  have hzVM := (mem_outN.mp hz).1
  rw [← huniform x hx y hy z hzVM]
  exact (mem_outN.mp hz).2

/-- Failure to be a tight cycle module has an explicit degree or exterior witness. -/
theorem nonmodule_cycle_variation {D : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hm : ∀ x ∈ M, q + 1 ≤ (outN D V x).card) (hnt : ¬ TightCycleModule q D V M) :
    (∃ x ∈ M, q + 2 ≤ (outN D V x).card) ∨
      ∃ x ∈ M, ∃ y ∈ M, ∃ z ∈ V \ M, D x z ≠ D y z := by
  classical
  by_cases hh : ∃ x ∈ M, q + 2 ≤ (outN D V x).card
  · exact Or.inl hh
  · right
    by_contra hn
    apply hnt
    apply tight_cycle_module_of_uniform_exterior hMV hM hcyc
    · intro x hx
      have hmin := hm x hx
      have hmax : ¬ q + 2 ≤ (outN D V x).card := fun h => hh ⟨x, hx, h⟩
      omega
    · intro x hx y hy z hz
      by_contra hne
      exact hn ⟨x, hx, y, hy, z, hz, hne⟩

/-- The small-ball branch supplies a local cycle with explicit non-module behavior. -/
theorem remaining_six_small_ball_cycle_variation {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23) :
    ∃ M : Finset ℕ, M ⊆ (ball D V u 3).erase u ∧ M.card = 6 ∧ OutEq 1 D M ∧
      ((∃ x ∈ M, 7 ≤ (outN D V x).card) ∨
        ∃ x ∈ M, ∃ y ∈ M, ∃ z ∈ V \ M, D x z ≠ D y z) := by
  obtain ⟨M, hsub, hcard, hcyc⟩ := remaining_six_small_ball_local_cycle hf hu hm hp hsmall
  have hMV : M ⊆ V := hsub.trans ((Finset.erase_subset _ _).trans ball_subset)
  exact ⟨M, hsub, hcard, hcyc, nonmodule_cycle_variation hMV hcard hcyc
    (fun x hx => hm x (hMV hx)) (no_local_tight_six_small_ball hf hsat hu hV hm hp hsmall hsub)⟩

/-- All vertices outside a set reached by one outgoing arc from the set. -/
noncomputable def exteriorHeads (D : CH.Digraph) (V M : Finset ℕ) : Finset ℕ :=
  open Classical in M.biUnion (fun x => outN D (V \ M) x)

/-- A shortest cycle with at most q distinct exterior heads is a tight module
when each ambient row has at least q+1 heads. -/
theorem tight_cycle_module_of_small_exterior {D : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hm : ∀ x ∈ M, q + 1 ≤ (outN D V x).card)
    (hext : (exteriorHeads D V M).card ≤ q) : TightCycleModule q D V M := by
  classical
  let Y := exteriorHeads D V M
  have hpart : M ∪ (V \ M) = V := Finset.union_sdiff_of_subset hMV
  have hrow (x : ℕ) (hx : x ∈ M) : outN D (V \ M) x ⊆ Y := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨x, hx, hz⟩
  have hsplit (x : ℕ) (hx : x ∈ M) :
      (outN D V x).card = 1 + (outN D (V \ M) x).card := by
    have h := card_outN_union (D := D)
      (show Disjoint M (V \ M) from Finset.disjoint_sdiff) x
    rwa [hpart, hcyc x hx] at h
  have hrows (x : ℕ) (hx : x ∈ M) : outN D (V \ M) x = Y := by
    apply Finset.eq_of_subset_of_card_le (hrow x hx)
    have hh := hm x hx
    have hs := hsplit x hx
    change Y.card ≤ q at hext
    omega
  obtain ⟨x, hx⟩ : M.Nonempty := Finset.card_pos.mp (by omega)
  have hY : Y.card = q := by
    have hs := hsplit x hx
    rw [hrows x hx] at hs
    have hh := hm x hx
    change Y.card ≤ q at hext
    omega
  have hYV : Y ⊆ V := by
    rw [← hrows x hx]
    exact outN_subset.trans Finset.sdiff_subset
  refine ⟨hMV, hM, hcyc, Y, hYV, hY, ?_, ?_⟩
  · intro y hy z hz
    exact (mem_outN.mp ((hrows y hy).symm ▸ hz)).2
  · intro y hy
    rw [hsplit y hy, hrows y hy, hY]
    omega

theorem nonmodule_cycle_exterior_ge {D : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hm : ∀ x ∈ M, q + 1 ≤ (outN D V x).card) (hnt : ¬ TightCycleModule q D V M) :
    q + 1 ≤ (exteriorHeads D V M).card := by
  by_contra hn
  exact hnt (tight_cycle_module_of_small_exterior hMV hM hcyc hm (by omega))

/-- Every local six-cycle in a small surviving profile has at least six
distinct exterior heads. Five exterior heads would force the forbidden module. -/
theorem local_six_small_ball_exterior_ge_six {D : CH.Digraph} {V M : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23)
    (hMsub : M ⊆ (ball D V u 3).erase u) (hM : M.card = 6) (hcyc : OutEq 1 D M) :
    6 ≤ (exteriorHeads D V M).card := by
  have hMV : M ⊆ V := hMsub.trans ((Finset.erase_subset _ _).trans ball_subset)
  exact nonmodule_cycle_exterior_ge hMV hM hcyc (fun x hx => hm x (hMV hx))
    (no_local_tight_six_small_ball hf hsat hu hV hm hp hsmall hMsub)

end LeanCH.BR.BRsub
