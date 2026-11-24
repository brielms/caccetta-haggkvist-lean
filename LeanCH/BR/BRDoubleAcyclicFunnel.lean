import LeanCH.BR.BRNearBoundaryRows

/-! Two acyclic stages with high first rows force short access to every exit. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

/-- Three closed middle vertices suffice for an `(s-2)`-step first-to-exit funnel. -/
theorem double_acyclic_funnel {D : CH.Digraph} {X Y T S : Finset ℕ} {s : ℕ}
    (hs : 6 ≤ s) (hX : X.card = s) (hY : Y.card = s) (hS : S.card = s)
    (hXY : Disjoint X Y) (hTY : T ⊆ Y) (hT3 : 3 ≤ T.card)
    (hacyX : QFree D X s) (hacyT : QFree D T T.card)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighT : ∀ t ∈ T, s ≤ (outN D (T ∪ S) t).card) :
    ∀ x ∈ X, ∀ w ∈ S, ∃ m, m ≤ s - 2 ∧ Walk D (X ∪ Y ∪ S) x w m := by
  classical
  let U := X ∪ Y ∪ S
  let rev : CH.Digraph := fun a b => D b a
  have hXU : X ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hTU : T ⊆ U := hTY.trans hYU
  have hSU : S ⊆ U := Finset.subset_union_right
  have hTc : T.card ≤ s := by have := Finset.card_le_card hTY; omega
  intro x hx w hw
  let A := fun k => X ∩ ball rev U w k
  let B := fun k => T ∩ ball rev U w k
  have hAX : ∀ k, A k ⊆ X := fun _ => Finset.inter_subset_left
  have hBT : ∀ k, B k ⊆ T := fun _ => Finset.inter_subset_left
  have hAmono : ∀ {i j}, i ≤ j → A i ⊆ A j := by
    intro i j hij v hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
      ball_mono_radius hij (Finset.mem_inter.mp hv).2⟩
  have hBmono : ∀ {i j}, i ≤ j → B i ⊆ B j := by
    intro i j hij v hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
      ball_mono_radius hij (Finset.mem_inter.mp hv).2⟩
  have hBstep : ∀ k, B k ≠ T → (B k).card + 1 ≤ (B (k + 1)).card := by
    intro k hne
    have hnonempty : (T \ B k).Nonempty := by
      by_contra hn
      have ht : T ⊆ B k := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp hn)
      exact hne (Finset.Subset.antisymm (hBT k) ht)
    obtain ⟨t, ht, hts⟩ := exists_sink (hacyT.mono_set Finset.sdiff_subset) hnonempty
      (Finset.card_le_card Finset.sdiff_subset)
    have htT := (Finset.mem_sdiff.mp ht).1
    have htB := (Finset.mem_sdiff.mp ht).2
    have htNext : t ∈ B (k + 1) := by
      by_contra hn
      have hsub : outN D (T ∪ S) t ⊆ S.erase w := by
        intro v hv
        obtain ⟨hvTS, htv⟩ := mem_outN.mp hv
        rcases Finset.mem_union.mp hvTS with hvT | hvS
        · by_cases hvB : v ∈ B k
          · exact (hn (Finset.mem_inter.mpr ⟨htT,
              ball_step (Finset.mem_inter.mp hvB).2 (hTU htT) htv⟩)).elim
          · exact (hts v (Finset.mem_sdiff.mpr ⟨hvT, hvB⟩) htv).elim
        · refine Finset.mem_erase.mpr ⟨?_, hvS⟩
          intro hvw
          apply hn
          exact Finset.mem_inter.mpr ⟨htT,
            ball_step (self_mem_ball (k := k) (hSU hw)) (hTU htT) (hvw ▸ htv)⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hw, hS] at hc
      have hh := hhighT t htT
      omega
    have hstrict : B k ⊂ B (k + 1) := Finset.ssubset_iff_subset_ne.mpr
      ⟨hBmono (Nat.le_succ k), fun heq => htB (heq.symm ▸ htNext)⟩
    exact Finset.card_lt_card hstrict
  have hBmin : ∀ k, min k T.card ≤ (B k).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases heq : B k = T
      · have hc := Finset.card_le_card (hBmono (Nat.le_succ k))
        rw [heq] at hc
        exact (Nat.min_le_right _ _).trans hc
      · have hc := hBstep k heq
        omega
  have hAstep : ∀ k, A (k + 1) ≠ X →
      (A k).card + (B k).card ≤ (A (k + 1)).card := by
    intro k hne
    have hnonempty : (X \ A (k + 1)).Nonempty := by
      by_contra hn
      have ht : X ⊆ A (k + 1) := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp hn)
      exact hne (Finset.Subset.antisymm (hAX _) ht)
    obtain ⟨v, hv, hvs⟩ := exists_sink (hacyX.mono_set Finset.sdiff_subset) hnonempty
      ((Finset.card_le_card Finset.sdiff_subset).trans hX.le)
    have hvX := (Finset.mem_sdiff.mp hv).1
    have hvNext := (Finset.mem_sdiff.mp hv).2
    have hsubX : outN D X v ⊆ A (k + 1) \ A k := by
      intro t ht
      obtain ⟨htX, hvt⟩ := mem_outN.mp ht
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · by_contra htNext
        exact hvs t (Finset.mem_sdiff.mpr ⟨htX, htNext⟩) hvt
      · intro htA
        exact hvNext (Finset.mem_inter.mpr ⟨hvX,
          ball_step (Finset.mem_inter.mp htA).2 (hXU hvX) hvt⟩)
    have hsubY : outN D Y v ⊆ Y \ B k := by
      intro t ht
      obtain ⟨htY, hvt⟩ := mem_outN.mp ht
      refine Finset.mem_sdiff.mpr ⟨htY, ?_⟩
      intro htB
      exact hvNext (Finset.mem_inter.mpr ⟨hvX,
        ball_step (Finset.mem_inter.mp htB).2 (hXU hvX) hvt⟩)
    have hcX := Finset.card_le_card hsubX
    have hcY := Finset.card_le_card hsubY
    rw [Finset.card_sdiff_of_subset ((hBT k).trans hTY), hY] at hcY
    have hcB := Finset.card_le_card ((hBT k).trans hTY)
    rw [hY] at hcB
    have hcA : (A (k + 1) \ A k).card + (A k).card = (A (k + 1)).card :=
      Finset.card_sdiff_add_card_eq_card (hAmono (Nat.le_succ k))
    have hh := hhighX v hvX
    rw [card_outN_union hXY] at hh
    omega
  have hfull : A (s - 2) = X := by
    by_contra hnot
    have hne : ∀ k, k ≤ s - 2 → A k ≠ X := by
      intro k hk heq
      apply hnot
      exact Finset.Subset.antisymm (hAX _) (fun v hv => hAmono hk (heq.symm ▸ hv))
    have hb1 := hBmin 1
    have hb2 := hBmin 2
    have hb3 := hBmin 3
    have ha2 := hAstep 1 (hne 2 (by omega))
    have ha3 := hAstep 2 (hne 3 (by omega))
    have ha4 := hAstep 3 (hne 4 (by omega))
    change (A 1).card + (B 1).card ≤ (A 2).card at ha2
    change (A 2).card + (B 2).card ≤ (A 3).card at ha3
    change (A 3).card + (B 3).card ≤ (A 4).card at ha4
    have hstart : 6 ≤ (A 4).card := by omega
    have hlinear : ∀ n, n + 4 ≤ s - 2 → n + 6 ≤ (A (n + 4)).card := by
      intro n
      induction n with
      | zero => intro _; exact hstart
      | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        have hg := hAstep (n + 4) (hne _ (by omega))
        have hb := hBmin (n + 4)
        rw [show n + 4 + 1 = n + 1 + 4 by omega] at hg
        omega
    have hc := hlinear (s - 6) (by omega)
    rw [show s - 6 + 4 = s - 2 by omega] at hc
    exact hnot (Finset.eq_of_subset_of_card_le (hAX _) (by rw [hX]; omega))
  have hxA : x ∈ A (s - 2) := hfull.symm ▸ hx
  obtain ⟨_, m, hm, wm⟩ := mem_ball.mp (Finset.mem_inter.mp hxA).2
  exact ⟨m, hm, wm.reverse_of_mem (hSU hw)⟩

end LeanCH.BR.BRsGen
