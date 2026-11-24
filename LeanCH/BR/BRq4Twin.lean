import LeanCH.BR.BRq4Pi

/-!
# Ball(q,4) route: Lemma 9 (no twins), its corollary, and Lemma 10 (two hosts) (Lean 4.35.0)

Paper: `BallQ4_attempt_subagent.md` §3, Lemma 9, Corollary, Lemma 10. Level `k = j + 3`, `|V♮| = 4k+3`.

* `no_twin` (**Lemma 9**): in a `k`-free out-4 host on `≤ 4k+1` vertices with `BallSmall k 4`, two distinct vertices
  have different out-neighbourhoods.
* `r0_K` (**Corollary of Lemma 9**): `R0` at some π-target forces `|K| ≤ 1`.
* `two_R0` (**Lemma 10**): no `p` has two distinct π-targets that are both `R0`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRsGen

/-- **Lemma 9 (no twins in an extremal host).** -/
theorem no_twin {H : CH.Digraph} {U : Finset ℕ} {k : ℕ} (hk : 1 ≤ k) (hS : BallSmall k 4) (hfree : QFree H U k)
    (hout : OutEq 4 H U) (hcard : U.card ≤ 4 * k + 1) {c c' : ℕ} (hc : c ∈ U) (hc' : c' ∈ U) (hne : c ≠ c')
    (heq : outN H U c = outN H U c') : False := by
  have hnot : c' ∉ ball H U c (k - 1) := by
    intro h
    obtain ⟨_, i, hi, w⟩ := mem_ball.mp h
    cases i with
    | zero => exact hne (walk_zero w)
    | succ i =>
      obtain ⟨v, hv, hcv, w'⟩ := walk_uncons_s w
      have hv' : v ∈ outN H U c' := by rw [← heq]; exact mem_outN.mpr ⟨hv, hcv⟩
      exact hfree c' (i + 1) (by omega) (by omega) (.step hv (mem_outN.mp hv').2 w')
  have hin := in_compl_b hk hS hfree hout hcard hc
  have h1 : c' ∈ U.filter (fun a => H a c = true) := by rw [hin]; exact Finset.mem_sdiff.mpr ⟨hc', hnot⟩
  have h2 : c ∈ outN H U c := by rw [heq]; exact mem_outN.mpr ⟨hc, (Finset.mem_filter.mp h1).2⟩
  exact loopfree hfree hk hc (mem_outN.mp h2).2

variable {D : CH.Digraph} {W : Finset ℕ} {u j : ℕ}

/-- In `R0`, `|B^F_k(z)| ≤ 4k+1`, `N_1 ⊆ B`, `K ⊆ B`. -/
theorem r0_facts (hfree : QFree D W (j + 5)) (hu : u ∈ W) (hV : (VV D W u j).card = 4 * (j + 3) + 3) {p z : ℕ}
    (hp : p ∈ ball D W u (j + 3)) (hp1 : p ∉ ball D W u (j + 2))
    (hM : ∀ x ∈ VV D W u j, x ∉ BB D W u j z ↔ (x = p ∨ Ap D W u j p x)) :
    (BB D W u j z).card ≤ 4 * (j + 3) + 1 ∧ (∀ v ∈ outN D W u, v ∈ BB D W u j z) ∧
      (∀ c ∈ KK D W u j, c ∈ BB D W u j z) := by
  classical
  obtain ⟨a, ha⟩ := exists_Ap (j := j) hu hp hp1
  have hap : a ≠ p := by rintro rfl; exact hp1 ha.1
  have hpV := pV_of hu hp hp1
  have haV := Ap_V hu ha
  have hpM : p ∈ VV D W u j \ BB D W u j z := Finset.mem_sdiff.mpr ⟨hpV, (hM p hpV).mpr (Or.inl rfl)⟩
  have haM : a ∈ VV D W u j \ BB D W u j z := Finset.mem_sdiff.mpr ⟨haV, (hM a haV).mpr (Or.inr ha)⟩
  have hpa : ({p, a} : Finset ℕ) ⊆ VV D W u j \ BB D W u j z := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hpM
    · rw [Finset.mem_singleton.mp hx]; exact haM
  have hM2 := Finset.card_le_card hpa
  rw [Finset.card_pair hap.symm] at hM2
  have hBV : (VV D W u j \ BB D W u j z).card + (BB D W u j z).card = (VV D W u j).card :=
    Finset.card_sdiff_add_card_eq_card ball_subset
  refine ⟨by omega, fun v hv => ?_, fun c hc => ?_⟩
  · obtain ⟨hvW, huv⟩ := mem_outN.mp hv
    have hv1 : v ∈ ball D W u 1 := ball_of_adj hvW huv
    have hvV : v ∈ VV D W u j := by
      refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) hv1⟩
      rintro rfl; exact loopfree hfree (by omega) hu huv
    by_contra hvB
    rcases (hM v hvV).mp hvB with rfl | hv'
    · exact hp1 (ball_mono_radius (by omega) hv1)
    · exact hv'.2.1 (ball_mono_radius (by omega) hv1)
  · obtain ⟨hc4, hc3⟩ := Finset.mem_sdiff.mp hc
    have hcV : c ∈ VV D W u j := memV_of hu hc4 hc3
    by_contra hcB
    rcases (hM c hcV).mp hcB with rfl | hc'
    · exact hc3 hp
    · exact hc3 (ball_mono_radius (by omega) hc'.1)

/-- **Corollary of Lemma 9.** `R0` forces `|K| ≤ 1`. -/
theorem r0_K (hS : BallSmall (j + 3) 4) (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W)
    (hV : (VV D W u j).card = 4 * (j + 3) + 3) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hp1 : p ∉ ball D W u (j + 2)) (hpz : D p z = true) (hzW : z ∈ W) (hR : R0 D W u j p z) :
    (KK D W u j).card ≤ 1 := by
  classical
  obtain ⟨hM, hex⟩ := hR
  have hzV := toV hfree hu hp hpz hzW
  obtain ⟨H, hHout, hHfree, -, hkeep, -⟩ := exists_pad_s (G := FF D W u j) (W := VV D W u j) (k := j + 3)
    (s := 4) (z := z) (X := ∅) (by omega) (FF_qfree hfree) (FF_outEq hfree hout hu) hzV
    (fun x hx => absurd hx (Finset.notMem_empty x)) (fun y hy => by simpa using hex y hy)
  rw [Finset.union_empty] at hHout hHfree
  have hHout' : OutEq 4 H (BB D W u j z) := hHout
  have hHfree' : QFree H (BB D W u j z) (j + 3) := hHfree
  obtain ⟨hBcard, hN1B, hKB⟩ := r0_facts hfree hu hV hp hp1 hM
  have hKout : ∀ c ∈ KK D W u j, outN H (BB D W u j z) c = outN D W u := by
    intro c hc
    have hcB := hKB c hc
    have hsub : outN D W u ⊆ outN H (BB D W u j z) c := by
      intro v hv
      have hvB := hN1B v hv
      refine mem_outN.mpr ⟨hvB, hkeep c hcB v hvB ?_⟩
      rw [FF_of_mem hc]; exact (mem_outN.mp hv).2
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hHout' c hcB, hout u hu])).symm
  by_contra h2
  obtain ⟨c, hc, c', hc', hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (KK D W u j).card)
  exact no_twin (k := j + 3) (by omega) hS hHfree' hHout' hBcard (hKB c hc) (hKB c' hc') hne
    (by rw [hKout c hc, hKout c' hc'])

/-- **Lemma 10 (two hosts).** -/
theorem two_R0 (hS : BallSmall (j + 3) 4) (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W)
    (hV : (VV D W u j).card = 4 * (j + 3) + 3) {p z1 z2 : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hp1 : p ∉ ball D W u (j + 2)) (hpz1 : D p z1 = true) (hz1W : z1 ∈ W) (hpz2 : D p z2 = true)
    (hz2W : z2 ∈ W) (hne : z1 ≠ z2) (hR1 : R0 D W u j p z1) (hR2 : R0 D W u j p z2) : False := by
  classical
  obtain ⟨hM1, hex1⟩ := hR1
  obtain ⟨hM2, hex2⟩ := hR2
  have hz1V := toV hfree hu hp hpz1 hz1W
  have hz2V := toV hfree hu hp hpz2 hz2W
  have hBeq : ball (FF D W u j) (VV D W u j) z2 (j + 3) = BB D W u j z1 := by
    ext x
    constructor
    · intro hx
      have hxV : x ∈ VV D W u j := ball_subset hx
      by_contra hx1
      exact ((hM2 x hxV).mpr ((hM1 x hxV).mp hx1)) hx
    · intro hx
      have hxV : x ∈ VV D W u j := ball_subset hx
      by_contra hx2
      exact ((hM1 x hxV).mpr ((hM2 x hxV).mp hx2)) hx
  obtain ⟨H1, hH1out, hH1free, -, hkeep1, hnew1⟩ := exists_pad_s (G := FF D W u j) (W := VV D W u j)
    (k := j + 3) (s := 4) (z := z1) (X := ∅) (by omega) (FF_qfree hfree) (FF_outEq hfree hout hu) hz1V
    (fun x hx => absurd hx (Finset.notMem_empty x)) (fun y hy => by simpa using hex1 y hy)
  obtain ⟨H2, hH2out, hH2free, -, -, hnew2⟩ := exists_pad_s (G := FF D W u j) (W := VV D W u j)
    (k := j + 3) (s := 4) (z := z2) (X := ∅) (by omega) (FF_qfree hfree) (FF_outEq hfree hout hu) hz2V
    (fun x hx => absurd hx (Finset.notMem_empty x)) (fun y hy => by simpa using hex2 y hy)
  rw [Finset.union_empty] at hH1out hH1free hH2out hH2free
  rw [hBeq] at hH2out hH2free hnew2
  have hH1out' : OutEq 4 H1 (BB D W u j z1) := hH1out
  have hH1free' : QFree H1 (BB D W u j z1) (j + 3) := hH1free
  obtain ⟨hBcard, -, -⟩ := r0_facts hfree hu hV hp hp1 hM1
  have hz1B : z1 ∈ BB D W u j z1 := self_mem_ball hz1V
  have in1 := in_eq_b (j := j + 3) (by omega) hS hH1free' hH1out' hBcard z1 hz1B
  have in2 := in_eq_b (j := j + 3) (by omega) hS hH2free hH2out hBcard z1 hz1B
  have sub2 : (BB D W u j z1).filter (fun a => H2 a z1 = true) ⊆
      (BB D W u j z1).filter (fun a => FF D W u j a z1 = true) := by
    intro a ha
    obtain ⟨haB, h⟩ := Finset.mem_filter.mp ha
    rcases hnew2 a haB z1 h with ⟨h', _⟩ | h' | h'
    · exact Finset.mem_filter.mpr ⟨haB, h'⟩
    · exact absurd h' hne
    · exact absurd h' (Finset.notMem_empty _)
  -- the vertex `b ∈ R_1`: the parent of `a ∈ A_p`
  obtain ⟨a, ha⟩ := exists_Ap (j := j) hu hp hp1
  have haV := Ap_V hu ha
  have haB : a ∉ BB D W u j z1 := (hM1 a haV).mpr (Or.inr ha)
  obtain ⟨b, hb, hba⟩ := ball_succ_pred hu ha.1 ha.2.1
  have hbj : b ∉ ball D W u j := fun h => ha.2.1 (ball_step h (ball_subset ha.1) hba)
  have hbV : b ∈ VV D W u j := memV_of hu (ball_mono_radius (by omega) hb) hbj
  have hbK : b ∉ KK D W u j := fun h => (Finset.mem_sdiff.mp h).2 (ball_mono_radius (by omega) hb)
  have hbB : b ∈ BB D W u j z1 := by
    by_contra hbB
    rcases (hM1 b hbV).mp hbB with rfl | hb'
    · exact hp1 (ball_mono_radius (by omega) hb)
    · exact hb'.2.1 hb
  have hFba : FF D W u j b a = true := by rw [FF_of_not_mem hbK]; exact hba
  have haE : a ∈ exitN (FF D W u j) (VV D W u j) (BB D W u j z1) z1 b :=
    Finset.mem_filter.mpr ⟨mem_outN.mpr ⟨haV, hFba⟩, Or.inr haB⟩
  have hnF : ¬ FF D W u j b z1 = true := by
    intro h
    have hzE : z1 ∈ exitN (FF D W u j) (VV D W u j) (BB D W u j z1) z1 b :=
      Finset.mem_filter.mpr ⟨mem_outN.mpr ⟨hz1V, h⟩, Or.inl rfl⟩
    have haz : a ≠ z1 := by rintro rfl; exact haB hz1B
    have := Finset.card_le_card (show ({a, z1} : Finset ℕ) ⊆ exitN (FF D W u j) (VV D W u j) (BB D W u j z1) z1 b by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haE
      · rw [Finset.mem_singleton.mp hx]; exact hzE)
    rw [Finset.card_pair haz] at this
    have := hex1 b hbB
    omega
  have hH1 : H1 b z1 = true := by
    by_contra h
    have hsub : outN H1 (BB D W u j z1) b ⊆ (outN (FF D W u j) (VV D W u j) b).erase a := by
      intro x hx
      obtain ⟨hxB, hbx⟩ := mem_outN.mp hx
      rcases hnew1 b hbB x hbx with ⟨h', _⟩ | rfl | h'
      · refine Finset.mem_erase.mpr ⟨?_, mem_outN.mpr ⟨ball_subset hxB, h'⟩⟩
        rintro rfl; exact haB hxB
      · exact absurd hbx h
      · exact absurd h' (Finset.notMem_empty _)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (mem_outN.mpr ⟨haV, hFba⟩), FF_outEq hfree hout hu b hbV,
      hH1out' b hbB] at h1
    omega
  have sub1 : insert b ((BB D W u j z1).filter (fun a => FF D W u j a z1 = true)) ⊆
      (BB D W u j z1).filter (fun a => H1 a z1 = true) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨hbB, hH1⟩
    · obtain ⟨hxB, hF⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxB, hkeep1 x hxB z1 hz1B hF⟩
  have hbF : b ∉ (BB D W u j z1).filter (fun a => FF D W u j a z1 = true) :=
    fun h => hnF (Finset.mem_filter.mp h).2
  have c1 := Finset.card_le_card sub1
  rw [Finset.card_insert_of_notMem hbF, in1] at c1
  have c2 := Finset.card_le_card sub2
  rw [in2] at c2
  omega

end LeanCH.BR.BRq4
