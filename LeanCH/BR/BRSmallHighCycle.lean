import LeanCH.BR.BRShortestCycle
import LeanCH.BR.BRWideFirstFunnel
import LeanCH.BR.BRsGenDiam

/-! A shortest-cycle obstruction for a small sinkless graph with many high rows. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem cycle_extension_parent_count {D : CH.Digraph} {V M P : Finset ℕ} {q x : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hMc : M.card = q + 1)
    (ho : OutEq 1 D M) (hxV : x ∈ V) (hxM : x ∉ M)
    (hPM : P ⊆ M) (hparents : ∀ a ∈ P, D a x = true)
    (hxout : 1 ≤ (outN D M x).card) :
    P.card ≤ 2 ∧ (2 ≤ (outN D M x).card → P.card + 1 ≤ 2) := by
  classical
  let U := insert x M
  have hMU : M ⊆ U := Finset.subset_insert _ _
  have hUV : U ⊆ V := Finset.insert_subset hxV hMV
  have hUc : U.card = q + 2 := by rw [Finset.card_insert_of_notMem hxM, hMc]
  have hxU : x ∈ U := Finset.mem_insert_self _ _
  have hmin : ∀ v ∈ U, 1 ≤ (outN D U v).card := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hxout.trans (Finset.card_le_card (outN_mono hMU _))
    · rw [← ho v hv]
      exact Finset.card_le_card (outN_mono hMU v)
  have hhigh : ∀ a ∈ P, 2 ≤ (outN D U a).card := by
    intro a ha
    have hxnot : x ∉ outN D M a := fun h => hxM (outN_subset h)
    have hsub : insert x (outN D M a) ⊆ outN D U a :=
      Finset.insert_subset (mem_outN.mpr ⟨hxU, hparents a ha⟩) (outN_mono hMU a)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxnot, ho a (hPM ha)] at hc
    exact hc
  have hc := small_one_core_high_count (by omega : 1 ≤ q) (hf.mono_set hUV)
    hmin ⟨x, hxU⟩ (by omega) (hPM.trans hMU) hhigh
  refine ⟨by omega, ?_⟩
  intro hh
  have hxP : x ∉ P := fun h => hxM (hPM h)
  have hhigh' : ∀ a ∈ insert x P, 2 ≤ (outN D U a).card := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hh.trans (Finset.card_le_card (outN_mono hMU _))
    · exact hhigh a ha
  have hc' := small_one_core_high_count (by omega : 1 ≤ q) (hf.mono_set hUV)
    hmin ⟨x, hxU⟩ (by omega) (Finset.insert_subset hxU (hPM.trans hMU)) hhigh'
  rw [Finset.card_insert_of_notMem hxP] at hc'
  omega

theorem cycle_extension_out_cap {D : CH.Digraph} {V M : Finset ℕ} {q x a : ℕ}
    (hq : 1 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hMc : M.card = q + 1)
    (ho : OutEq 1 D M) (hxV : x ∈ V) (hxM : x ∉ M)
    (ha : a ∈ M) (hax : D a x = true) (hxout : 1 ≤ (outN D M x).card) :
    (outN D M x).card ≤ 2 := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hxout
  obtain ⟨hwM, hxw⟩ := mem_outN.mp hw
  have heq : ball D M w q = M :=
    diam_small_s hq (ball_q_one q hq) (hf.mono_set hMV) ho (by omega) w hwM
  obtain ⟨_, k, _, wk⟩ := mem_ball.mp (heq.symm ▸ ha)
  let U := insert x M
  have hMU : M ⊆ U := Finset.subset_insert _ _
  have hUV : U ⊆ V := Finset.insert_subset hxV hMV
  have hxU : x ∈ U := Finset.mem_insert_self _ _
  have wc : Walk D U x x (k + 1 + 1) :=
    (Walk.step (hMU hwM) hxw (wk.mono hMU)).snoc hxU hax
  have hc := cyclic_row_degree_cap hq (hf.mono_set hUV) (by omega) wc
  have hUc : U.card = q + 2 := by rw [Finset.card_insert_of_notMem hxM, hMc]
  have hm : (outN D M x).card ≤ (outN D U x).card :=
    Finset.card_le_card (outN_mono hMU x)
  omega

/-- If 3<=d<=q+1, a q-free sinkless graph on q+d vertices has fewer than d
vertices of out-degree at least d. The d>=3 guard is essential. -/
theorem small_one_high_degree_count {D : CH.Digraph} {V H : Finset ℕ} {q d : ℕ}
    (hq : 2 ≤ q) (hd : 3 ≤ d) (hdq : d ≤ q + 1) (hf : QFree D V q)
    (hV : V.card = q + d) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, d ≤ (outN D V v).card) : H.card < d := by
  classical
  by_contra hn
  have hH : d ≤ H.card := by omega
  have hneH : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, M, hqp, hfree, hMV, hMc, ho⟩ :=
    exists_minimal_cycle_support (by omega) hf hmin (hneH.mono hHV)
  let T := V \ M
  let P := H ∩ M
  let K := H \ P
  have hTV : T ⊆ V := Finset.sdiff_subset
  have hPM : P ⊆ M := Finset.inter_subset_right
  have hPH : P ⊆ H := Finset.inter_subset_left
  have hKT : K ⊆ T := by
    intro x hx
    obtain ⟨hxH, hxP⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hHV hxH, fun hxM => hxP (Finset.mem_inter.mpr ⟨hxH, hxM⟩)⟩
  have hsplit : M ∪ T = V := Finset.union_sdiff_of_subset hMV
  have hdisj : Disjoint M T := Finset.disjoint_sdiff
  have hTc : T.card + M.card = V.card := Finset.card_sdiff_add_card_eq_card hMV
  have hKc : K.card + P.card = H.card := Finset.card_sdiff_add_card_eq_card hPH
  have hKle : K.card ≤ T.card := Finset.card_le_card hKT
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hPne
  have hrow (v : ℕ) : (outN D V v).card = (outN D M v).card + (outN D T v).card := by
    rw [← hsplit, card_outN_union hdisj]
  have haout := hhigh a (hPH ha)
  rw [hrow a, ho a (hPM ha)] at haout
  have haT : (outN D T a).card ≤ T.card := Finset.card_le_card outN_subset
  have hpq : p = q := by omega
  subst p
  have hTeq : T.card = d - 1 := by omega
  have hfull : ∀ v ∈ P, ∀ x ∈ T, D v x = true := by
    intro v hv
    have hh := hhigh v (hPH hv)
    rw [hrow v, ho v (hPM hv)] at hh
    have heq : outN D T v = T := Finset.eq_of_subset_of_card_le outN_subset (by omega)
    intro x hx
    exact (mem_outN.mp (heq.symm ▸ hx)).2
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z, hz, hsink⟩ := exists_sink (hf.mono_set hTV) hTne (by omega)
  have hzM : z ∉ M := (Finset.mem_sdiff.mp hz).2
  have hzclosed : outN D V z ⊆ outN D M z := by
    intro w hw
    obtain ⟨hwV, hzw⟩ := mem_outN.mp hw
    refine mem_outN.mpr ⟨?_, hzw⟩
    by_contra hn
    exact hsink w (Finset.mem_sdiff.mpr ⟨hwV, hn⟩) hzw
  have hzout : 1 ≤ (outN D M z).card :=
    (hmin z (hTV hz)).trans (Finset.card_le_card hzclosed)
  have hparents := cycle_extension_parent_count hq hf hMV hMc ho (hTV hz) hzM
    hPM (fun v hv => hfull v hv z hz) hzout
  have hPcap : P.card ≤ 2 := hparents.1
  have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hKne
  have hxT := hKT hx
  have hxH := (Finset.mem_sdiff.mp hx).1
  have hxV := hHV hxH
  have hxM := (Finset.mem_sdiff.mp hxT).2
  have hxnot : x ∉ outN D T x := fun h => loopfree hf (by omega) hxV (mem_outN.mp h).2
  have hsubT : outN D T x ⊆ T.erase x := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨fun h => hxnot (h ▸ hw), outN_subset hw⟩
  have hcapT := Finset.card_le_card hsubT
  rw [Finset.card_erase_of_mem hxT] at hcapT
  have hxhigh := hhigh x hxH
  rw [hrow x] at hxhigh
  have hxout : 2 ≤ (outN D M x).card := by omega
  have hPone := (cycle_extension_parent_count hq hf hMV hMc ho hxV hxM
    hPM (fun v hv => hfull v hv x hxT) (by omega)).2 hxout
  have hKT_eq : K = T := Finset.eq_of_subset_of_card_le hKT (by omega)
  have hzH : z ∈ H := (Finset.mem_sdiff.mp (hKT_eq.symm ▸ hz)).1
  have hzHigh : d ≤ (outN D M z).card :=
    (hhigh z hzH).trans (Finset.card_le_card hzclosed)
  have hzCap := cycle_extension_out_cap (by omega) hf hMV hMc ho (hTV hz) hzM
    (hPM ha) (hfull a ha z hz) hzout
  omega

/-- A smaller host also obeys the high-row bound when d<=q. -/
theorem small_one_high_degree_count_of_le {D : CH.Digraph} {V H : Finset ℕ} {q d : ℕ}
    (hd : 3 ≤ d) (hdq : d ≤ q) (hf : QFree D V q)
    (hV : V.card ≤ q + d) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, d ≤ (outN D V v).card) : H.card < d := by
  classical
  by_contra hn
  have hH : d ≤ H.card := by omega
  obtain ⟨X, hXH, hXc⟩ := Finset.exists_subset_card_eq hH
  have hXV := hXH.trans hHV
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv, hsink⟩ := exists_sink (hf.mono_set hXV) hXne (by omega)
  have hsub : outN D V v ⊆ V \ X := by
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨outN_subset hw,
      fun hwX => hsink w hwX (mem_outN.mp hw).2⟩
  have hc := Finset.card_le_card hsub
  have hh := hhigh v (hXH hv)
  have hpart := Finset.card_sdiff_add_card_eq_card hXV
  have hVlo : 2 * d ≤ V.card := by omega
  have hcount := small_one_high_degree_count (q := V.card - d) (by omega) hd
    (by omega) (hf.mono_bound (by omega)) (by omega) hmin hHV hhigh
  omega

end LeanCH.BR.BRsGen
