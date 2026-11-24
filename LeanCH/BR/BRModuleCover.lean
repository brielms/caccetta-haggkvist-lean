import LeanCH.BR.BRModuleLayers

/-! Disjoint cycle modules and the global assembly of their proved local budgets. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

/-- A nonempty proper cut of a shortest cycle support has an outgoing crossing. -/
theorem cycle_cut_crossing {D : CH.Digraph} {M A : Finset ℕ} {q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D M q) (hM : M.card = q + 1)
    (ho : OutEq 1 D M) (hAM : A ⊆ M) (hAn : A.Nonempty) (hproper : A ≠ M) :
    ∃ a ∈ A, ∃ b ∈ M \ A, D a b = true := by
  classical
  by_contra hn
  have hretain : ∀ a ∈ A, outN D M a ⊆ outN D A a := by
    intro a ha b hb
    refine mem_outN.mpr ⟨?_, (mem_outN.mp hb).2⟩
    by_contra hbA
    exact hn ⟨a, ha, b, Finset.mem_sdiff.mpr ⟨outN_subset hb, hbA⟩, (mem_outN.mp hb).2⟩
  have hmin : ∀ a ∈ A, 1 ≤ (outN D A a).card := by
    intro a ha
    rw [← ho a (hAM ha)]
    exact Finset.card_le_card (hretain a ha)
  have hc := dt_size hq (ball_q_one q hq) (hf.mono_set hAM) hmin hAn
  exact hproper (Finset.eq_of_subset_of_card_le hAM (by omega))

theorem module_outside_uniform {D : CH.Digraph} {V M Y : Finset ℕ} {q s : ℕ}
    (hqs : q + 1 = s) (hq : 2 ≤ q) (hf : QFree D V q)
    (hMV : M ⊆ V) (hYV : Y ⊆ V) (hY : Y.card = s - 1)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = s) (hcyc : OutEq 1 D M) :
    ∀ z ∈ V, z ∉ M → ∀ x ∈ M, ∀ y ∈ M, D x z = true → D y z = true := by
  intro z hz hzM x hx y hy hxz
  rcases out_sub hqs hq hf hMV hYV hY hhead hout hcyc hx hz hxz with h | h
  · exact (hzM h).elim
  · exact hhead y hy z h

/-- The data required by Lemma M, with the exterior set retained as an existential. -/
structure TightCycleModule (q : ℕ) (D : CH.Digraph) (V M : Finset ℕ) : Prop where
  subset : M ⊆ V
  card : M.card = q + 1
  cycle : OutEq 1 D M
  exterior : ∃ Y : Finset ℕ, Y ⊆ V ∧ Y.card = q ∧
    (∀ x ∈ M, ∀ y ∈ Y, D x y = true) ∧ (∀ x ∈ M, (outN D V x).card = q + 1)

abbrev TightSixModule (D : CH.Digraph) (V M : Finset ℕ) : Prop := TightCycleModule 5 D V M

/-- Distinct tight cycle modules are disjoint at every cutoff q>=2. -/
theorem tight_cycle_modules_disjoint {D : CH.Digraph} {V M N : Finset ℕ} {q : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hsat : Sat q D V)
    (hM : TightCycleModule q D V M) (hN : TightCycleModule q D V N) (hne : M ≠ N) :
    Disjoint M N := by
  classical
  by_contra hn
  have hI : (M ∩ N).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hn
  have hMN : ¬ M ⊆ N := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h (by rw [hM.card, hN.card]))
  have hNM : ¬ N ⊆ M := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h (by rw [hM.card, hN.card])).symm
  have hR : (M \ N).Nonempty := by
    by_contra h
    exact hMN (fun x hx => by
      by_contra hxN
      exact h ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxN⟩⟩)
  obtain ⟨z, hzN, hzM⟩ : ∃ z ∈ N, z ∉ M := by
    by_contra h
    exact hNM (fun z hz => by by_contra hzM; exact h ⟨z, hz, hzM⟩)
  have hIproper : M ∩ N ≠ M := by
    intro heq
    exact hMN (heq ▸ Finset.inter_subset_right)
  have hRproper : M \ N ≠ M := by
    intro heq
    obtain ⟨x, hx⟩ := hI
    obtain ⟨hxM, hxN⟩ := Finset.mem_inter.mp hx
    exact (Finset.mem_sdiff.mp (heq.symm ▸ hxM)).2 hxN
  obtain ⟨a, ha, b, hb, hab⟩ := cycle_cut_crossing (by omega : 1 ≤ q)
    (hf.mono_set hM.subset) hM.card hM.cycle Finset.inter_subset_left hI hIproper
  obtain ⟨p, hp, x, hx, hpx⟩ := cycle_cut_crossing (by omega : 1 ≤ q)
    (hf.mono_set hM.subset) hM.card hM.cycle Finset.sdiff_subset hR hRproper
  have haM := (Finset.mem_inter.mp ha).1
  have haN := (Finset.mem_inter.mp ha).2
  have hbM := (Finset.mem_sdiff.mp hb).1
  have hbN : b ∉ N := fun h => (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mpr ⟨hbM, h⟩)
  have hpM := (Finset.mem_sdiff.mp hp).1
  have hpN := (Finset.mem_sdiff.mp hp).2
  have hxM := (Finset.mem_sdiff.mp hx).1
  have hxN : x ∈ N := by
    by_contra h
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mpr ⟨hxM, h⟩)
  obtain ⟨Y, hYV, hY, hheadsM, houtM⟩ := hM.exterior
  obtain ⟨Z, hZV, hZ, hheadsN, houtN⟩ := hN.exterior
  have hinN := module_parent_uniform (s := q + 1) rfl hq hf hsat
    hN.subset hZV (by omega) hheadsN houtN hN.cycle
  have houtMu := module_outside_uniform (s := q + 1) rfl hq hf
    hM.subset hYV (by omega) hheadsM houtM hM.cycle
  have houtNu := module_outside_uniform (s := q + 1) rfl hq hf
    hN.subset hZV (by omega) hheadsN houtN hN.cycle
  have hpz := hinN p (hM.subset hpM) hpN x hxN z hzN hpx
  have hbz := houtMu z (hN.subset hzN) hzM p hpM b hbM hpz
  have hzb := houtNu b (hM.subset hbM) hbN a haN z hzN hab
  exact digonfree hf hq (hM.subset hbM) (hN.subset hzN) hbz hzb

theorem tight_six_modules_disjoint {D : CH.Digraph} {V M N : Finset ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V)
    (hM : TightSixModule D V M) (hN : TightSixModule D V N) (hne : M ≠ N) :
    Disjoint M N := tight_cycle_modules_disjoint (by decide) hf hsat hM hN hne

/-- Outside vertices with at least one head in the module. -/
noncomputable def moduleParents (D : CH.Digraph) (V M : Finset ℕ) : Finset ℕ :=
  open Classical in (V \ M).filter (fun p => ∃ x ∈ M, D p x = true)

theorem module_parents_eq_WM {D : CH.Digraph} {V M Y : Finset ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V)
    (hMV : M ⊆ V) (hM : M.card = 6) (hcyc : OutEq 1 D M)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = 6) :
    moduleParents D V M = WM D V M Y 5 := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpVM, x, hx, hpx⟩ := Finset.mem_filter.mp hp
    have hpin : p ∈ inN D V x := mem_inN.mpr ⟨(Finset.mem_sdiff.mp hpVM).1, hpx⟩
    rw [lemmaM (by decide : 5 + 1 = 6) (by decide) hf hsat hMV hYV hY hhead hout hcyc hx] at hpin
    rcases Finset.mem_union.mp hpin with h | h
    · exact ((Finset.mem_sdiff.mp hpVM).2 (mem_inN.mp h).1).elim
    · exact h
  · intro hp
    obtain ⟨x, hx⟩ : M.Nonempty := Finset.card_pos.mp (by omega)
    have hpin : p ∈ inN D V x := by
      rw [lemmaM (by decide : 5 + 1 = 6) (by decide) hf hsat hMV hYV hY hhead hout hcyc hx]
      exact Finset.mem_union_right _ hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨(mem_WM.mp hp).1, (mem_WM.mp hp).2.1⟩,
      x, hx, (mem_inN.mp hpin).2⟩

theorem TightSixModule.parent_card_le_four {D : CH.Digraph} {V M : Finset ℕ}
    (h : TightSixModule D V M) (hf : QFree D V 5) (hsat : Sat 5 D V)
    (hV : V.card = 31) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) :
    (moduleParents D V M).card ≤ 4 := by
  obtain ⟨Y, hYV, hY, hhead, hout⟩ := h.exterior
  rw [module_parents_eq_WM hf hsat h.subset h.card h.cycle hYV hY hhead hout]
  exact tightModule_WM_le_four hf hV hm h.subset hYV h.card hY hhead

theorem TightSixModule.parent_deficit_le_one {D : CH.Digraph} {V M : Finset ℕ}
    (h : TightSixModule D V M) (hf : QFree D V 5) (hsat : Sat 5 D V)
    (hV : V.card = 31) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    {p : ℕ} (hp : p ∈ moduleParents D V M) :
    (inN D V p).card - (outN D V p).card ≤ 1 := by
  obtain ⟨Y, hYV, hY, hhead, hout⟩ := h.exterior
  rw [module_parents_eq_WM hf hsat h.subset h.card h.cycle hYV hY hhead hout] at hp
  have hh := tight_six_parent_deficit_le_one hf hsat hV hm h.subset h.card hYV hY hhead hout h.cycle hp
  omega

theorem TightSixModule.surplus_ge_one {D : CH.Digraph} {V M : Finset ℕ}
    (h : TightSixModule D V M) (hf : QFree D V 5) (hsat : Sat 5 D V)
    (hV : V.card = 31) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    {x : ℕ} (hx : x ∈ M) :
    1 ≤ (outN D V x).card - (inN D V x).card := by
  obtain ⟨Y, hYV, hY, hhead, hout⟩ := h.exterior
  have hinternal := (dt_reg (by decide : 1 ≤ 5) (ball_q_one 5 (by decide))
    (hf.mono_set h.subset) (fun x hx => (h.cycle x hx).ge) (by rw [h.card])).2
  have hi := tightModule_in_le_five hf hsat hV hm h.subset hYV h.card hY hhead hout
    (fun v hv => ⟨h.cycle v hv, hinternal v hv⟩) hx
  have ho := hout x hx
  omega

theorem degree_deficit_surplus_sum (D : CH.Digraph) (V : Finset ℕ) :
    (∑ v ∈ V, ((inN D V v).card - (outN D V v).card)) =
      ∑ v ∈ V, ((outN D V v).card - (inN D V v).card) := by
  have hp : ∀ v ∈ V, (outN D V v).card + ((inN D V v).card - (outN D V v).card) =
      (inN D V v).card + ((outN D V v).card - (inN D V v).card) := by
    intro v hv; omega
  have hs := Finset.sum_congr rfl hp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  omega

/-- A tight root already parents a tight cycle module, uniformly on the subdiagonal. -/
theorem module_of_tight_root {D : CH.Digraph} {V : Finset ℕ} {s u : ℕ}
    (hs : 3 ≤ s) (hf : QFree D V (s - 1)) (hu : u ∈ V) (ht : TightRoot D V s u) :
    TightCycleModule (s - 1) D V (outN D V u) ∧ u ∈ moduleParents D V (outN D V u) := by
  classical
  obtain ⟨hc, hsecond, hrows⟩ := ht
  refine ⟨⟨outN_subset, by omega, fun x hx => (hrows x hx).2.1, ?_⟩, ?_⟩
  · refine ⟨ball D V u 2 \ ball D V u 1, Finset.sdiff_subset.trans ball_subset,
      hsecond, ?_, ?_⟩
    · intro x hx y hy
      exact (hrows x hx).2.2.2 y (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
    · intro x hx
      have hh := (hrows x hx).1
      omega
  · have hunot : u ∉ outN D V u := fun h => loopfree hf (by omega) hu (mem_outN.mp h).2
    obtain ⟨x, hx⟩ : (outN D V u).Nonempty := Finset.card_pos.mp (by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hu, hunot⟩, x, hx, (mem_outN.mp hx).2⟩

/-- All of the global count is proved; the module-cover supplier is an explicit input. -/
theorem incoming_regular_of_six_module_cover {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hcover : ∀ v ∈ V, 7 ≤ (inN D V v).card →
      ∃ M, TightSixModule D V M ∧ v ∈ moduleParents D V M) :
    ∀ v ∈ V, (inN D V v).card = 6 := by
  classical
  let F := V.powerset.filter (TightSixModule D V)
  let H := V.filter (fun v => 7 ≤ (inN D V v).card)
  let U := F.biUnion id
  let W := F.biUnion (moduleParents D V)
  let deficit := fun v => (inN D V v).card - (outN D V v).card
  let surplus := fun v => (outN D V v).card - (inN D V v).card
  have hF : ∀ M ∈ F, TightSixModule D V M := fun _ h => (Finset.mem_filter.mp h).2
  have hHF : ∀ v ∈ H, ∃ M ∈ F, v ∈ moduleParents D V M := by
    intro v hv
    obtain ⟨hvV, hv7⟩ := Finset.mem_filter.mp hv
    obtain ⟨M, hM, hvM⟩ := hcover v hvV hv7
    exact ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hM.subset, hM⟩, hvM⟩
  have hHW : H ⊆ W := by
    intro v hv
    obtain ⟨M, hMF, hvM⟩ := hHF v hv
    exact Finset.mem_biUnion.mpr ⟨M, hMF, hvM⟩
  have hparent : ∀ M ∈ F, (moduleParents D V M).card ≤ 4 :=
    fun M hMF => (hF M hMF).parent_card_le_four hf hsat hV hm
  have hHc : H.card ≤ 4 * F.card := by
    have h1 := Finset.card_le_card hHW
    have h2 : W.card ≤ ∑ M ∈ F, (moduleParents D V M).card := Finset.card_biUnion_le
    have h3 := Finset.sum_le_sum hparent
    simp only [Finset.sum_const_nat (fun _ _ => rfl)] at h3
    omega
  have hpair : Set.PairwiseDisjoint (F : Set (Finset ℕ)) (fun M : Finset ℕ => M) := by
    intro M hMF N hNF hne
    exact tight_six_modules_disjoint hf hsat (hF M hMF) (hF N hNF) hne
  have hUc : U.card = 6 * F.card := by
    have hh : U.card = ∑ M ∈ F, M.card := Finset.card_biUnion hpair
    rw [hh, Finset.sum_congr rfl (fun M hMF => (hF M hMF).card)]
    simp only [Finset.sum_const_nat (fun _ _ => rfl)]
    omega
  have hUV : U ⊆ V := by
    intro x hx
    obtain ⟨M, hMF, hxM⟩ := Finset.mem_biUnion.mp hx
    exact (hF M hMF).subset hxM
  have hgain : ∀ x ∈ U, 1 ≤ surplus x := by
    intro x hx
    obtain ⟨M, hMF, hxM⟩ := Finset.mem_biUnion.mp hx
    exact (hF M hMF).surplus_ge_one hf hsat hV hm hxM
  have hgainSum : U.card ≤ ∑ x ∈ V, surplus x := by
    have hh := Finset.sum_le_sum hgain
    simp only [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_one] at hh
    exact hh.trans (Finset.sum_le_sum_of_subset hUV)
  have hdef : ∀ v ∈ H, deficit v ≤ 1 := by
    intro v hv
    obtain ⟨M, hMF, hvM⟩ := hHF v hv
    exact (hF M hMF).parent_deficit_le_one hf hsat hV hm hvM
  have hzero : ∀ v ∈ V \ H, deficit v = 0 := by
    intro v hv
    obtain ⟨hvV, hvH⟩ := Finset.mem_sdiff.mp hv
    have hn : ¬ 7 ≤ (inN D V v).card := fun h => hvH (Finset.mem_filter.mpr ⟨hvV, h⟩)
    have ho := hm v hvV
    dsimp only [deficit]
    omega
  have hdefSum : (∑ v ∈ V, deficit v) ≤ H.card := by
    have hh := Finset.sum_le_sum hdef
    have hz := Finset.sum_eq_zero hzero
    have hs := Finset.sum_sdiff (show H ⊆ V from Finset.filter_subset _ _) (f := deficit)
    simp only [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_one] at hh
    omega
  have hbalance : (∑ v ∈ V, deficit v) = ∑ v ∈ V, surplus v := degree_deficit_surplus_sum D V
  have hFc : F.card = 0 := by omega
  have hH0 : H.card = 0 := by omega
  have hin : ∀ v ∈ V, (inN D V v).card ≤ 6 := by
    intro v hv
    by_contra hn
    have hvH : v ∈ H := Finset.mem_filter.mpr ⟨hv, by omega⟩
    rw [Finset.card_eq_zero.mp hH0] at hvH
    exact Finset.notMem_empty _ hvH
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hlo := Finset.sum_le_sum hm
  have hhi := Finset.sum_le_sum hin
  have heq : (∑ v ∈ V, (inN D V v).card) = ∑ _v ∈ V, 6 := le_antisymm hhi (he ▸ hlo)
  exact (Finset.sum_eq_sum_iff_of_le hin).mp heq

/-- The remaining structural supplier, not an asserted theorem. -/
def SixModuleCover : Prop :=
  ∀ D : CH.Digraph, QFree D (Finset.range 31) 5 →
    (∀ v ∈ Finset.range 31, 6 ≤ (outN D (Finset.range 31) v).card) →
    Sat 5 D (Finset.range 31) → ∀ v ∈ Finset.range 31,
      7 ≤ (inN D (Finset.range 31) v).card →
        ∃ M, TightSixModule D (Finset.range 31) M ∧ v ∈ moduleParents D (Finset.range 31) M

theorem six_module_cover_of_non_tight
    (h : ∀ D : CH.Digraph, QFree D (Finset.range 31) 5 →
      (∀ v ∈ Finset.range 31, 6 ≤ (outN D (Finset.range 31) v).card) →
      Sat 5 D (Finset.range 31) → ∀ v ∈ Finset.range 31,
        ¬ TightRoot D (Finset.range 31) 6 v → 7 ≤ (inN D (Finset.range 31) v).card →
          ∃ M, TightSixModule D (Finset.range 31) M ∧
            v ∈ moduleParents D (Finset.range 31) M) : SixModuleCover := by
  intro D hf hm hsat v hv hv7
  by_cases ht : TightRoot D (Finset.range 31) 6 v
  · exact ⟨outN D (Finset.range 31) v, module_of_tight_root (by decide) hf hv ht⟩
  · exact h D hf hm hsat v hv ht hv7

theorem br_five_six_of_module_cover (h : SixModuleCover) : Compose.Boundary.BoundaryRegular 5 6 := by
  apply br_of_satQ
  intro D hf hm hsat
  exact incoming_regular_of_six_module_cover hf hsat (by simp) hm (h D hf hm hsat)

theorem ntc6_other_of_module_cover (h : SixModuleCover) : NTC6OtherFirstPairs := by
  intro D hf hm hsat u hu hp hne
  have hi := incoming_regular_of_six_module_cover hf hsat (by simp) hm (h D hf hm hsat) u hu
  have hc := card_inN_of_satQ (by decide : 1 ≤ 5) hf hsat hu
  change (inN D (Finset.range 31) u).card + (ball D (Finset.range 31) u 4).card = _ at hc
  rw [Finset.card_range] at hc
  have hb := hp.deficient
  omega

end LeanCH.BR.BRsub
