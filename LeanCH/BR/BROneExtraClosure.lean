import LeanCH.BR.BRAcyclicExtraTriple
import LeanCH.BR.BRDoubleAcyclicFunnel

/-! Closure of the unequal triple with sizes (s,s,s+1) and floors s,s,2. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s c x : ℕ}

/-- A middle-to-first return isolates its middle vertex also from all third rows. -/
theorem OneExtraTriple.middle_return_control (h : OneExtraTriple D X Y Z s)
    (hc : c ∈ Y) (hx : x ∈ X) (hcx : D c x = true) :
    (∀ y ∈ Y.erase c, ∀ a ∈ X, ¬ D y a = true) ∧
    (∀ y ∈ Y.erase c, ¬ D y c = true) ∧ (∀ z ∈ Z, ¬ D z c = true) := by
  have hs := h.large
  have hf := h.free
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  obtain ⟨hreach, hnX, hnc⟩ := first_back_arc_control hs
    (hf.mono_set Finset.subset_union_left) h.disjoint_first h.card_first h.card_second
    h.high_first hx hc hcx
  refine ⟨hnX, hnc, ?_⟩
  intro z hz hzc
  obtain ⟨y, hy, hyz⟩ := h.parents z hz
  by_cases hyc : y = c
  · exact digonfree hf (by omega) (hYU hc) (hZU hz) (hyc ▸ hyz) hzc
  · obtain ⟨m, hm, wm⟩ := hreach y (Finset.mem_erase.mpr ⟨hyc, hy⟩)
    exact hf x (m + 1 + 1 + 1) (by omega) (by omega)
      ((((wm.mono Finset.subset_union_left).snoc (hZU hz) hyz).snoc (hYU hc) hzc).snoc (hXU hx) hcx)

/-- The complete one-extra configuration is impossible for every s >= 6. -/
theorem OneExtraTriple.false (h : OneExtraTriple D X Y Z s) : False := by
  classical
  have hs := h.large
  have hf := h.free
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  obtain ⟨z, hz, a, ha, hza⟩ := h.forced_return
  obtain ⟨b, hb, hbz⟩ := h.parents z hz
  let S := Z.erase z
  have hSZ : S ⊆ Z := Finset.erase_subset _ _
  have hSU : S ⊆ X ∪ Y ∪ Z := hSZ.trans hZU
  have hSc : S.card = s := by
    simp only [S, Finset.card_erase_of_mem hz, h.card_third, Nat.add_sub_cancel]
  have hnoSz : ∀ w ∈ S, ¬ D w z = true :=
    fun w hw => h.return_no_third_parent hz ha hza w (hSZ hw)
  obtain ⟨R, hRY, hRlo, hRhi, _, hRclosed, hRnoz⟩ :=
    acyclic_parent_return_basin hs hf h.acyclic_first h.disjoint_first h.card_first
      h.card_second h.high_first ha hb hz hbz hza
  have hK : ∃ K : Finset ℕ, K ⊆ Y ∧ s - 1 ≤ K.card ∧ K.card ≤ s ∧ (Y \ K).card ≤ 1 ∧
      (∀ y ∈ K, ∀ v ∈ X, ¬ D y v = true) ∧
      (∀ y ∈ K, ∀ v ∈ Y, D y v = true → v ∈ K) ∧
      (∀ w ∈ S, ∀ v ∈ Y, D w v = true → v ∈ K) := by
    by_cases hback : ∃ c ∈ Y, ∃ x ∈ X, D c x = true
    · obtain ⟨c, hc, x, hx, hcx⟩ := hback
      obtain ⟨hnoX, hnoc, hnoZc⟩ := h.middle_return_control hc hx hcx
      have hKc : (Y.erase c).card = s - 1 := by rw [Finset.card_erase_of_mem hc, h.card_second]
      refine ⟨Y.erase c, Finset.erase_subset _ _, by omega, by omega, ?_, hnoX, ?_, ?_⟩
      · rw [Finset.card_sdiff_of_subset (Finset.erase_subset _ _), h.card_second, hKc]
        omega
      · intro y hy v hv hyv
        exact Finset.mem_erase.mpr ⟨fun heq => hnoc y hy (heq ▸ hyv), hv⟩
      · intro w hw v hv hwv
        exact Finset.mem_erase.mpr ⟨fun heq => hnoZc w (hSZ hw) (heq ▸ hwv), hv⟩
    · refine ⟨Y, Finset.Subset.refl _, by rw [h.card_second]; omega, h.card_second.le,
        by simp, ?_, ?_, ?_⟩
      · intro y hy v hv hyv
        exact hback ⟨y, hy, v, hv, hyv⟩
      · exact fun _ _ _ hv _ => hv
      · exact fun _ _ _ hv _ => hv
  obtain ⟨K, hKY, hKlo, hKhi, hKoutside, hKnoX, hKclosed, hSK⟩ := hK
  let T := R ∩ K
  have hTR : T ⊆ R := Finset.inter_subset_left
  have hTK : T ⊆ K := Finset.inter_subset_right
  have hTY : T ⊆ Y := hTR.trans hRY
  have hTlo : 3 ≤ T.card := by
    have hsub : R ⊆ T ∪ (Y \ K) := by
      intro r hr
      by_cases hrK : r ∈ K
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hr, hrK⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hRY hr, hrK⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hThi : T.card ≤ s - 1 := (Finset.card_le_card hTR).trans hRhi
  have hhighT : ∀ t ∈ T, s ≤ (outN D (T ∪ S) t).card := by
    intro t ht
    have hsub : outN D (X ∪ Y ∪ Z) t ⊆ outN D (T ∪ S) t := by
      intro v hv
      obtain ⟨hvU, htv⟩ := mem_outN.mp hv
      refine mem_outN.mpr ⟨?_, htv⟩
      rcases Finset.mem_union.mp hvU with hvXY | hvZ
      · rcases Finset.mem_union.mp hvXY with hvX | hvY
        · exact (hKnoX t (hTK ht) v hvX htv).elim
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
            ⟨hRclosed t (hTR ht) v hvY htv, hKclosed t (hTK ht) v hvY htv⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_erase.mpr ⟨fun heq => hRnoz t (hTR ht) (heq ▸ htv), hvZ⟩)
    exact (h.high_second t (hTY ht)).trans (Finset.card_le_card hsub)
  have hnoSX : ∀ w ∈ S, ∀ v ∈ X, ¬ D w v = true := by
    intro w hw v hv hwv
    obtain ⟨m, hm, wm⟩ := double_acyclic_funnel hs h.card_first h.card_second hSc
      h.disjoint_first hTY hTlo h.acyclic_first
      ((hf.mono_set (hTY.trans hYU)).mono_bound hThi) h.high_first hhighT v hv w hw
    have hsmall : X ∪ Y ∪ S ⊆ X ∪ Y ∪ Z :=
      Finset.union_subset_union (Finset.Subset.refl _) hSZ
    exact hf v (m + 1) (by omega) (by omega) ((wm.mono hsmall).snoc (hXU hv) hwv)
  have hWsub : K ∪ S ⊆ X ∪ Y ∪ Z := Finset.union_subset (hKY.trans hYU) hSU
  have hhighK : ∀ y ∈ K, s - 1 ≤ (outN D (K ∪ S) y).card := by
    intro y hy
    have hsub : outN D (X ∪ Y ∪ Z) y ⊆ insert z (outN D (K ∪ S) y) := by
      intro v hv
      obtain ⟨hvU, hyv⟩ := mem_outN.mp hv
      by_cases hvz : v = z
      · exact Finset.mem_insert.mpr (Or.inl hvz)
      · apply Finset.mem_insert_of_mem
        refine mem_outN.mpr ⟨?_, hyv⟩
        rcases Finset.mem_union.mp hvU with hvXY | hvZ
        · rcases Finset.mem_union.mp hvXY with hvX | hvY
          · exact (hKnoX y hy v hvX hyv).elim
          · exact Finset.mem_union_left _ (hKclosed y hy v hvY hyv)
        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hvz, hvZ⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hh := h.high_second y (hKY hy)
    omega
  have hlowS : ∀ w ∈ S, 2 ≤ (outN D (K ∪ S) w).card := by
    intro w hw
    have hsub : outN D (X ∪ Y ∪ Z) w ⊆ outN D (K ∪ S) w := by
      intro v hv
      obtain ⟨hvU, hwv⟩ := mem_outN.mp hv
      refine mem_outN.mpr ⟨?_, hwv⟩
      rcases Finset.mem_union.mp hvU with hvXY | hvZ
      · rcases Finset.mem_union.mp hvXY with hvX | hvY
        · exact (hnoSX w hw v hvX hwv).elim
        · exact Finset.mem_union_left _ (hSK w hw v hvY hwv)
      · exact Finset.mem_union_right _
          (Finset.mem_erase.mpr ⟨fun heq => hnoSz w hw (heq ▸ hwv), hvZ⟩)
    exact (h.low_third w (hSZ hw)).trans (Finset.card_le_card hsub)
  have hmin : ∀ v ∈ K ∪ S, 2 ≤ (outN D (K ∪ S) v).card := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvK | hvS
    · exact (by omega : 2 ≤ s - 1).trans (hhighK v hvK)
    · exact hlowS v hvS
  have hKS : Disjoint K S :=
    (h.disjoint_third.mono_left Finset.subset_union_right).mono hKY hSZ
  have hc : (K ∪ S).card = K.card + s := by rw [Finset.card_union_of_disjoint hKS, hSc]
  exact two_core_many_high_false (by omega : 1 ≤ s - 1) (hf.mono_set hWsub)
    (by omega) hmin (H := K) Finset.subset_union_left (by omega)
    (fun v hv => (by omega : 5 ≤ s - 1).trans (hhighK v hv))

/-- The formerly open uniform unequal-triple target is now supplied. -/
theorem one_extra_triple_impossible : OneExtraTripleImpossible := by
  intro s D X Y Z h
  exact h.false

/-- Uniform excess-two target, proved in `BRTwoExtraCyclic.two_extra_triple_impossible`. -/
def TwoExtraTripleImpossible : Prop :=
  ∀ (s : ℕ) (D : CH.Digraph) (X Y Z : Finset ℕ), 6 ≤ s →
    QFree D (X ∪ Y ∪ Z) (s - 1) → Disjoint X Y → Disjoint (X ∪ Y) Z →
    X.card = s → Y.card = s → Z.card = s + 2 →
    (∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card) →
    (∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card) →
    (∀ z ∈ Z, 3 ≤ (outN D (X ∪ Y ∪ Z) z).card) →
    (∀ z ∈ Z, ∃ y ∈ Y, D y z = true) → False

end LeanCH.BR.BRsGen
