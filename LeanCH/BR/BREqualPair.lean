import LeanCH.BR.BR45Base
import LeanCH.BR.BRNarrowPair
import LeanCH.BR.BRFiniteWalk

/-! Equal consecutive sets: a uniform exclusion of back arcs. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y : Finset ℕ} {s : ℕ}

/-- A return to a cyclic first set forces all other second-set rows to avoid that set. -/
theorem cyclic_back_arc_others (hs : 5 ≤ s)
    (hf : QFree D (X ∪ Y) (s - 1)) (hdisj : Disjoint X Y)
    (hX : X.card = s) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card)
    {b a : ℕ} (hb : b ∈ Y) (ha : a ∈ X) (hba : D b a = true) :
    (∀ y ∈ Y.erase b, D a y = true) ∧
    (∀ y ∈ Y.erase b, ∀ x ∈ X, ¬ D y x = true) ∧
    (∀ y ∈ Y.erase b, ¬ D y b = true) := by
  classical
  have hXU : X ⊆ X ∪ Y := Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y := Finset.subset_union_right
  have hfX := hf.mono_set hXU
  have hreg := (dt_reg (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega))
    hfX hint (by rw [hX]; omega)).1
  let A := ball D X a (s - 3)
  have hAX : A ⊆ X := ball_subset
  have hAc : s - 2 ≤ A.card := by
    have := ball_one_growth hfX hint ha (s - 3) (by omega)
    change s - 2 ≤ (ball D X a (s - 3)).card
    omega
  have hmiss : ∀ x ∈ A, ¬ D x b = true := by
    intro x hx hxb
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hx
    exact hf a (m + 1 + 1) (by omega) (by omega)
      (((w.mono hXU).snoc (hYU hb) hxb).snoc (hXU ha) hba)
  have hall : ∀ x ∈ A, ∀ y ∈ Y.erase b, D x y = true := by
    intro x hx
    have hsub : outN D Y x ⊆ Y.erase b := by
      intro y hy
      obtain ⟨hyY, hxy⟩ := mem_outN.mp hy
      exact Finset.mem_erase.mpr ⟨fun h => hmiss x hx (h ▸ hxy), hyY⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem hb, hY]
      have hh := hhigh x (hAX hx)
      rw [card_outN_union hdisj, hreg x (hAX hx)] at hh
      omega)
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  have hnear : ∀ x ∈ X, ∃ z ∈ A, z ∈ ball D X x 2 := by
    intro x hx
    have hc := ball_one_growth hfX hint hx 2 (by omega)
    have hi : (A ∩ ball D X x 2).Nonempty := by
      by_contra hn
      have hd : Disjoint A (ball D X x 2) := Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hn)
      have hu := Finset.card_le_card (Finset.union_subset hAX
        (ball_subset (D := D) (W := X) (u := x) (k := 2)))
      rw [Finset.card_union_of_disjoint hd, hX] at hu
      omega
    obtain ⟨z, hz⟩ := hi
    exact ⟨z, (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩
  have hnoX : ∀ y ∈ Y.erase b, ∀ x ∈ X, ¬ D y x = true := by
    intro y hy x hx hyx
    obtain ⟨z, hzA, hz⟩ := hnear x hx
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hz
    exact hf x (m + 1 + 1) (by omega) (by omega)
      (((w.mono hXU).snoc (hYU (Finset.mem_of_mem_erase hy)) (hall z hzA y hy)).snoc (hXU hx) hyx)
  refine ⟨hall a (self_mem_ball ha), hnoX, ?_⟩
  intro y hy hyb
  exact hf a 3 (by decide) (by omega)
    (.step (hYU (Finset.mem_of_mem_erase hy)) (hall a (self_mem_ball ha) y hy)
      (.step (hYU hb) hyb (.step (hXU ha) hba (.refl a))))

/-- The internal positive-degree branch of the equal-pair argument. -/
theorem equal_pair_no_back_of_internal (hs : 5 ≤ s)
    (hf : QFree D (X ∪ Y) (s - 1)) (hdisj : Disjoint X Y)
    (hX : X.card = s) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hlow : ∀ y ∈ Y, 1 ≤ (outN D (X ∪ Y) y).card)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card) :
    ∀ b ∈ Y, ∀ a ∈ X, ¬ D b a = true := by
  classical
  have hYU : Y ⊆ X ∪ Y := Finset.subset_union_right
  intro b hb a ha hba
  obtain ⟨_, hnoX, hnoB⟩ := cyclic_back_arc_others hs hf hdisj hX hY hhigh hint hb ha hba
  obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set ((Finset.erase_subset _ _).trans hYU))
    (show (Y.erase b).Nonempty by rw [← Finset.card_pos, Finset.card_erase_of_mem hb, hY]; omega)
    (by rw [Finset.card_erase_of_mem hb, hY])
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (hlow y (Finset.mem_of_mem_erase hy))
  obtain ⟨hzU, hyz⟩ := mem_outN.mp hz
  rcases Finset.mem_union.mp hzU with hzX | hzY
  · exact hnoX y hy z hzX hyz
  · have hzb : z ≠ b := by
      intro h
      exact hnoB y hy (h ▸ hyz)
    exact hsink z (Finset.mem_erase.mpr ⟨hzb, hzY⟩) hyz

private theorem forward_peel {Z U : Finset ℕ} {q : ℕ}
    (hf : QFree D U q) (hZU : Z ⊆ U) (hYU : Y ⊆ U)
    (hZ : Z.card ≤ q) (hY : Y.card = s)
    (hhigh : ∀ x ∈ Z, s ≤ (outN D (Z ∪ Y) x).card) :
    ∀ j, j ≤ Z.card → ∃ S ⊆ Z, S.card = j ∧
      ∀ x ∈ S, ∀ y ∈ Y, ∃ m, 1 ≤ m ∧ m ≤ j ∧ Walk D U x y m := by
  classical
  intro j
  induction j with
  | zero => exact fun _ => ⟨∅, Finset.empty_subset _, rfl,
      fun x hx => (Finset.notMem_empty x hx).elim⟩
  | succ j ih =>
    intro hj
    obtain ⟨S, hSZ, hSc, hSr⟩ := ih (by omega)
    have hTc : (Z \ S).card = Z.card - j := by rw [Finset.card_sdiff_of_subset hSZ, hSc]
    obtain ⟨t, ht, hsink⟩ := exists_sink (hf.mono_set (Finset.sdiff_subset.trans hZU))
      (show (Z \ S).Nonempty by rw [← Finset.card_pos, hTc]; omega) (by rw [hTc]; omega)
    obtain ⟨htZ, htS⟩ := Finset.mem_sdiff.mp ht
    have htr : ∀ y ∈ Y, ∃ m, 1 ≤ m ∧ m ≤ j + 1 ∧ Walk D U t y m := by
      by_cases hh : ∃ c ∈ Z, D t c = true
      · obtain ⟨c, hc, htc⟩ := hh
        have hcS : c ∈ S := by
          by_contra hn
          exact hsink c (Finset.mem_sdiff.mpr ⟨hc, hn⟩) htc
        intro y hy
        obtain ⟨m, hm, hmj, w⟩ := hSr c hcS y hy
        exact ⟨m + 1, by omega, by omega, .step (hZU hc) htc w⟩
      · have hsub : outN D (Z ∪ Y) t ⊆ Y := by
          intro c hc
          obtain ⟨hcU, htc⟩ := mem_outN.mp hc
          rcases Finset.mem_union.mp hcU with hcZ | hcY
          · exact (hh ⟨c, hcZ, htc⟩).elim
          · exact hcY
        have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hY]; exact hhigh t htZ)
        intro y hy
        exact ⟨1, le_rfl, by omega, .step (hYU hy) (mem_outN.mp (heq.symm ▸ hy)).2 (.refl y)⟩
    refine ⟨insert t S, Finset.insert_subset htZ hSZ,
      by rw [Finset.card_insert_of_notMem htS, hSc], ?_⟩
    intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact htr y hy
    · obtain ⟨m, hm, hmj, w⟩ := hSr x hx y hy
      exact ⟨m, hm, by omega, w⟩

private theorem one_escape_cap {U T : Finset ℕ} {e q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D U q) (hTU : T ⊆ U) (heU : e ∈ U)
    (heT : e ∉ T) (hT : T.card = q)
    (hmin : ∀ t ∈ T, 1 ≤ (outN D (T ∪ {e}) t).card) :
    (outN D T e).card ≤ 1 := by
  classical
  by_cases hpos : 1 ≤ (outN D T e).card
  · have hsub : T ∪ {e} ⊆ U := Finset.union_subset hTU (Finset.singleton_subset_iff.mpr heU)
    have hmin' : ∀ t ∈ T ∪ {e}, 1 ≤ (outN D (T ∪ {e}) t).card := by
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact hmin t ht
      · have hte := Finset.mem_singleton.mp ht
        subst t
        exact hpos.trans (Finset.card_le_card (outN_mono Finset.subset_union_left e))
    have hc : (T ∪ {e}).card = q * 1 + 1 := by
      rw [Finset.union_singleton, Finset.card_insert_of_notMem heT, hT]
      omega
    have hreg := (dt_reg hq (ball_q_one q hq) (hf.mono_set hsub) hmin' hc).1
      e (Finset.mem_union_right _ (Finset.mem_singleton_self e))
    exact (Finset.card_le_card (outN_mono Finset.subset_union_left e)).trans hreg.le
  · omega

private theorem equal_pair_all_but {a b x m : ℕ}
    (hs : 5 ≤ s) (hf : QFree D (X ∪ Y) (s - 1)) (hdisj : Disjoint X Y)
    (hY : Y.card = s) (ha : a ∈ X) (hb : b ∈ Y) (hba : D b a = true)
    (_hx : x ∈ X) (hh : s ≤ (outN D (X ∪ Y) x).card)
    (hi : (outN D X x).card ≤ 1) (hm : m ≤ s - 3) (w : Walk D X a x m) :
    ∀ y ∈ Y.erase b, D x y = true := by
  classical
  have hmiss : ¬ D x b = true := fun hxb => hf a (m + 1 + 1) (by omega) (by omega)
    (((w.mono Finset.subset_union_left).snoc (Finset.mem_union_right _ hb) hxb).snoc
      (Finset.mem_union_left _ ha) hba)
  have hsub : outN D Y x ⊆ Y.erase b := by
    intro y hy
    obtain ⟨hyY, hxy⟩ := mem_outN.mp hy
    exact Finset.mem_erase.mpr ⟨fun h => hmiss (h ▸ hxy), hyY⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem hb, hY]
    rw [card_outN_union hdisj] at hh
    omega)
  intro y hy
  exact (mem_outN.mp (heq.symm ▸ hy)).2

/-- The acyclic branch uses a shortest path to a sink; a back arc forces degree at most four. -/
theorem equal_pair_no_back_of_acyclic (hs : 5 ≤ s)
    (hf : QFree D (X ∪ Y) (s - 1)) (hdisj : Disjoint X Y)
    (hX : X.card = s) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hlow : ∀ y ∈ Y, 1 ≤ (outN D (X ∪ Y) y).card)
    (hacy : QFree D X s) :
    ∀ b ∈ Y, ∀ a ∈ X, ¬ D b a = true := by
  classical
  have hXU : X ⊆ X ∪ Y := Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y := Finset.subset_union_right
  have sinkY : ∀ t ∈ X, (∀ z ∈ X, ¬ D t z = true) → ∀ y ∈ Y, D t y = true := by
    intro t ht hts
    have hsub : outN D (X ∪ Y) t ⊆ Y := by
      intro z hz
      obtain ⟨hzU, htz⟩ := mem_outN.mp hz
      rcases Finset.mem_union.mp hzU with hzX | hzY
      · exact (hts z hzX htz).elim
      · exact hzY
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hY]; exact hhigh t ht)
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  intro b hb a ha hba
  obtain ⟨p⟩ := exists_shortest_sink_path hacy hX.le ha
  have hlen : p.len < s := by have := p.bounded; omega
  have hlong : s - 2 ≤ p.len := by
    by_contra hn
    have w := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start, Nat.sub_zero] at w
    exact hf a (p.len + 1 + 1) (by omega) (by omega)
      (((w.mono hXU).snoc (hYU hb) (sinkY _ (p.mem _ le_rfl) p.sink b hb)).snoc (hXU ha) hba)
  let P := (Finset.range (p.len + 1)).image p.vertex
  have hPX : P ⊆ X := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact p.mem i (by have := Finset.mem_range.mp hi; omega)
  have hPc : P.card = p.len + 1 := by
    exact (Finset.card_image_of_injOn (p.injective hacy hX.le)).trans (Finset.card_range _)
  have hPmem : ∀ i, i ≤ p.len → p.vertex i ∈ P := fun i hi =>
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have hPget : ∀ x ∈ P, ∃ i, i ≤ p.len ∧ p.vertex i = x := by
    intro x hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
    exact ⟨i, by have := Finset.mem_range.mp hi; omega, heq⟩
  have hchord {i j : ℕ} (hi : i ≤ p.len) (hj : j ≤ p.len)
      (hij : D (p.vertex i) (p.vertex j) = true) : j = i + 1 :=
    p.no_chord hacy hX.le hi hj hij
  have hYbU : Y.erase b ⊆ X ∪ Y := (Finset.erase_subset _ _).trans hYU
  by_cases hfull : p.len = s - 1
  · have hspan : P = X := Finset.eq_of_subset_of_card_le hPX (by omega)
    have hint1 : ∀ i, i ≤ p.len → (outN D X (p.vertex i)).card ≤ 1 := by
      intro i hi
      have hsub : outN D X (p.vertex i) ⊆ {p.vertex (i + 1)} := by
        intro x hx
        obtain ⟨hxX, hix⟩ := mem_outN.mp hx
        obtain ⟨j, hj, rfl⟩ := hPget x (hspan.symm ▸ hxX)
        exact Finset.mem_singleton.mpr (congrArg p.vertex (hchord hi hj hix))
      exact (Finset.card_le_card hsub).trans (by simp)
    have hall : ∀ i, i ≤ p.len → i ≤ s - 3 → ∀ y ∈ Y.erase b, D (p.vertex i) y = true := by
      intro i hi hir
      have w := p.walk (Nat.zero_le i) hi
      rw [p.start, Nat.sub_zero] at w
      exact equal_pair_all_but hs hf hdisj hY ha hb hba (p.mem i hi)
        (hhigh _ (p.mem i hi)) (hint1 i hi) hir w
    have hreach : ∀ x ∈ X, ∀ y ∈ Y.erase b,
        ∃ m, m ≤ s - 2 ∧ Walk D (X ∪ Y) x y m := by
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := hPget x (hspan.symm ▸ hx)
      by_cases hir : i ≤ s - 3
      · exact ⟨1, by omega, .step (hYbU hy) (hall i hi hir y hy) (.refl y)⟩
      · exact ⟨p.len - i + 1, by omega,
          ((p.walk hi le_rfl).mono hXU).snoc (hYbU hy)
            (sinkY _ (p.mem _ le_rfl) p.sink y (Finset.mem_of_mem_erase hy))⟩
    have hnoX : ∀ y ∈ Y.erase b, ∀ x ∈ X, ¬ D y x = true := by
      intro y hy x hx hyx
      obtain ⟨m, hm, w⟩ := hreach x hx y hy
      exact hf x (m + 1) (by omega) (by omega) (w.snoc (hXU hx) hyx)
    have hay : ∀ y ∈ Y.erase b, D a y = true := by
      simpa only [p.start] using hall 0 (Nat.zero_le _) (by omega)
    obtain ⟨y, hy, hys⟩ := exists_sink (hf.mono_set hYbU)
      (show (Y.erase b).Nonempty by rw [← Finset.card_pos, Finset.card_erase_of_mem hb, hY]; omega)
      (by rw [Finset.card_erase_of_mem hb, hY])
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (hlow y (Finset.mem_of_mem_erase hy))
    obtain ⟨hzU, hyz⟩ := mem_outN.mp hz
    rcases Finset.mem_union.mp hzU with hzX | hzY
    · exact hnoX y hy z hzX hyz
    · have hzb : z ≠ b := by
        intro h
        exact hf a 3 (by decide) (by omega)
          (.step (hYbU hy) (hay y hy) (.step (hYU hb) (h ▸ hyz) (.step (hXU ha) hba (.refl a))))
      exact hys z (Finset.mem_erase.mpr ⟨hzb, hzY⟩) hyz
  · have hp : p.len = s - 2 := by omega
    have hEc : (X \ P).card = 1 := by rw [Finset.card_sdiff_of_subset hPX, hX, hPc, hp]; omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (X \ P).card)
    obtain ⟨heX, heP⟩ := Finset.mem_sdiff.mp he
    have hsplit : ∀ x ∈ X, x ∈ P ∨ x = e := by
      intro x hx
      by_cases hxP : x ∈ P
      · exact Or.inl hxP
      · exact Or.inr (Finset.card_le_one.mp hEc.le x (Finset.mem_sdiff.mpr ⟨hx, hxP⟩) e he)
    have hsingle : ∀ i, i ≤ p.len → ¬ D (p.vertex i) e = true →
        (outN D X (p.vertex i)).card ≤ 1 := by
      intro i hi hne
      have hsub : outN D X (p.vertex i) ⊆ {p.vertex (i + 1)} := by
        intro x hx
        obtain ⟨hxX, hix⟩ := mem_outN.mp hx
        rcases hsplit x hxX with hxP | rfl
        · obtain ⟨j, hj, rfl⟩ := hPget x hxP
          exact Finset.mem_singleton.mpr (congrArg p.vertex (hchord hi hj hix))
        · exact (hne hix).elim
      exact (Finset.card_le_card hsub).trans (by simp)
    have hthin : ∃ x ∈ X, ∃ m, m ≤ s - 4 ∧ Walk D X a x m ∧ (outN D X x).card ≤ 1 := by
      by_cases hh : ∃ i, i ≤ s - 4 ∧ (outN D X (p.vertex i)).card ≤ 1
      · obtain ⟨i, hi, hic⟩ := hh
        have hil : i ≤ p.len := by omega
        have w := p.walk (Nat.zero_le i) hil
        rw [p.start, Nat.sub_zero] at w
        exact ⟨p.vertex i, p.mem i hil, i, hi, w, hic⟩
      · have hpe : ∀ i, i ≤ s - 4 → D (p.vertex i) e = true := by
          intro i hi
          by_contra hn
          exact hh ⟨i, hi, hsingle i (by omega) hn⟩
        have hae : D a e = true := by simpa only [p.start] using hpe 0 (by omega)
        have hecap : (outN D X e).card ≤ 1 := by
          have hsub : outN D X e ⊆ {p.vertex (s - 3)} := by
            intro x hx
            obtain ⟨hxX, hex⟩ := mem_outN.mp hx
            rcases hsplit x hxX with hxP | rfl
            · obtain ⟨j, hj, rfl⟩ := hPget x hxP
              have hjlow : ¬ j ≤ s - 4 := fun hj' =>
                digonfree hacy (by omega) heX (p.mem j hj) hex (hpe j hj')
              have hjlast : j ≠ p.len := by
                intro hj'
                have hmin := p.minimal (p.vertex p.len) (p.mem _ le_rfl) p.sink 2
                  (.step heX hae (.step (p.mem _ le_rfl) (hj' ▸ hex) (.refl _)))
                omega
              exact Finset.mem_singleton.mpr (congrArg p.vertex (by omega : j = s - 3))
            · exact (loopfree hacy (by omega) heX hex).elim
          exact (Finset.card_le_card hsub).trans (by simp)
        exact ⟨e, heX, 1, by omega, .step heX hae (.refl e), hecap⟩
    obtain ⟨w, hwX, k, hk, wak, hwcap⟩ := hthin
    have hwall := equal_pair_all_but hs hf hdisj hY ha hb hba hwX (hhigh w hwX) hwcap (by omega) wak
    have hareach : ∀ y ∈ Y.erase b, ∃ m, m ≤ s - 3 ∧ Walk D (X ∪ Y) a y m := by
      intro y hy
      exact ⟨k + 1, by omega, (wak.mono hXU).snoc (hYbU hy) (hwall y hy)⟩
    have hPreach : ∀ x ∈ P, ∀ y ∈ Y.erase b,
        ∃ m, m ≤ s - 2 ∧ Walk D (X ∪ Y) x y m := by
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := hPget x hx
      by_cases hi0 : i = 0
      · subst i
        rw [p.start]
        obtain ⟨m, hm, wm⟩ := hareach y hy
        exact ⟨m, by omega, wm⟩
      · exact ⟨p.len - i + 1, by omega,
          ((p.walk hi le_rfl).mono hXU).snoc (hYbU hy)
            (sinkY _ (p.mem _ le_rfl) p.sink y (Finset.mem_of_mem_erase hy))⟩
    have hnoP : ∀ y ∈ Y.erase b, ∀ x ∈ P, ¬ D y x = true := by
      intro y hy x hx hyx
      obtain ⟨m, hm, wm⟩ := hPreach x hx y hy
      exact hf x (m + 1) (by omega) (by omega) (wm.snoc (hXU (hPX hx)) hyx)
    have hnoB : ∀ y ∈ Y.erase b, ¬ D y b = true := by
      intro y hy hyb
      obtain ⟨m, hm, wm⟩ := hareach y hy
      exact hf a (m + 1 + 1) (by omega) (by omega)
        ((wm.snoc (hYU hb) hyb).snoc (hXU ha) hba)
    have hret : ∀ y ∈ Y.erase b, 1 ≤ (outN D (Y.erase b ∪ {e}) y).card := by
      intro y hy
      have hsub : outN D (X ∪ Y) y ⊆ outN D (Y.erase b ∪ {e}) y := by
        intro z hz
        obtain ⟨hzU, hyz⟩ := mem_outN.mp hz
        refine mem_outN.mpr ⟨?_, hyz⟩
        rcases Finset.mem_union.mp hzU with hzX | hzY
        · rcases hsplit z hzX with hzP | rfl
          · exact (hnoP y hy z hzP hyz).elim
          · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => hnoB y hy (h ▸ hyz), hzY⟩)
      exact (hlow y (Finset.mem_of_mem_erase hy)).trans (Finset.card_le_card hsub)
    have heY : e ∉ Y := fun heY => Finset.disjoint_left.mp hdisj heX heY
    have hcapY' := one_escape_cap (by omega : 1 ≤ s - 1) hf hYbU (hXU heX)
      (fun heYb => heY (Finset.mem_of_mem_erase heYb))
      (by rw [Finset.card_erase_of_mem hb, hY]) hret
    have hcapY : (outN D Y e).card ≤ 2 := by
      have heq : outN D (Y.erase b) e = (outN D Y e).erase b := by
        ext z
        simp only [mem_outN, Finset.mem_erase]
        tauto
      rw [heq] at hcapY'
      have := Finset.pred_card_le_card_erase (s := outN D Y e) (a := b)
      omega
    obtain ⟨z, hz, hzs⟩ := exists_sink (hf.mono_set hYbU)
      (show (Y.erase b).Nonempty by rw [← Finset.card_pos, Finset.card_erase_of_mem hb, hY]; omega)
      (by rw [Finset.card_erase_of_mem hb, hY])
    have hze : D z e = true := by
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (hret z hz)
      obtain ⟨hvZ, hzv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvZ with hvY | hvE
      · exact (hzs v hvY hzv).elim
      · simpa only [Finset.mem_singleton.mp hvE] using hzv
    have hcapX : (outN D X e).card ≤ 2 := by
      have hsub : outN D X e ⊆ {p.vertex 0, p.vertex 1} := by
        intro x hx
        obtain ⟨hxX, hex⟩ := mem_outN.mp hx
        rcases hsplit x hxX with hxP | rfl
        · obtain ⟨j, hj, rfl⟩ := hPget x hxP
          have hj2 : j < 2 := by
            by_contra hn
            have wt := (((p.walk hj le_rfl).mono hXU).snoc (hYbU hz)
              (sinkY _ (p.mem _ le_rfl) p.sink z (Finset.mem_of_mem_erase hz))).snoc (hXU heX) hze
            exact hf e (p.len - j + 1 + 1 + 1) (by omega) (by omega)
              (.step (hXU (p.mem j hj)) hex wt)
          have hj01 : j = 0 ∨ j = 1 := by omega
          rcases hj01 with rfl | rfl <;> simp
        · exact (loopfree hacy (by omega) heX hex).elim
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    have hh := hhigh e heX
    rw [card_outN_union hdisj] at hh
    omega

/-- For `s >= 5`, equal sets of size s with degree floors s and one admit no back arc. -/
theorem equal_pair_no_back (hs : 5 ≤ s)
    (hf : QFree D (X ∪ Y) (s - 1)) (hdisj : Disjoint X Y)
    (hX : X.card = s) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hlow : ∀ y ∈ Y, 1 ≤ (outN D (X ∪ Y) y).card) :
    ∀ b ∈ Y, ∀ a ∈ X, ¬ D b a = true := by
  classical
  by_cases hint : ∀ x ∈ X, 1 ≤ (outN D X x).card
  · exact equal_pair_no_back_of_internal hs hf hdisj hX hY hhigh hlow hint
  · push Not at hint
    obtain ⟨t, ht, htc⟩ := hint
    have hts : ∀ z ∈ X, ¬ D t z = true := by
      intro z hz htz
      have := Finset.card_pos.mpr ⟨z, mem_outN.mpr ⟨hz, htz⟩⟩
      omega
    have hacy : QFree D X s := by
      have h := qfree_succ_of_sink (hf.mono_set Finset.subset_union_left)
        (by rw [hX]; omega) ht hts
      convert h using 1 <;> omega
    exact equal_pair_no_back_of_acyclic hs hf hdisj hX hY hhigh hlow hacy

end LeanCH.BR.BRsGen
