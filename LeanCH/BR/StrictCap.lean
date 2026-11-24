import LeanCH.BR.LargeModule

/-!
# Strict degree cap (q = 3), Lean 4.35.0

Paper source: `checkpoints/boundary_20261112/LargeBoundaryModule_Exclusion_20261112.md`, Section 7
("Tight whole-out-neighbourhood banks are now excluded, without saturation"), audited in
`..._IndependentAudit.md` Section 5.

**Theorem (`strict_cap`).** Let `s ≥ 2`, `G` loopless on `3s+1` labels with minimum out-degree `≥ s`, no directed
cycle of length `≤ 3`, and `BR(3,t)` for every `1 ≤ t < s`. A vertex `v` with in-degree `s + a ≥ s` and out-degree
`s + f` satisfies `3a + 2f + 2 ≤ s`.

Proof. The weak cap (`LeanCH.BR.WeakCap.weak_cap`) gives `3a + 2f + 1 ≤ s`. Suppose equality. Then `r = a + f`
satisfies `1 ≤ r` (else `s = 1`) and `2r + 1 ≤ s`, so `r < s`. Put `K = V \ ({v} ∪ I(v))`, of size `2s - a`;
`O(v) ⊆ K` and every head of an out-neighbour of `v` lies in `K` (no digon, no triangle through `v`). With
`M(v) = K \ O(v)`, of size `s - r`, every `x ∈ O(v)` keeps at least `r` heads in `O(v)`, and
`|O(v)| = s + f = 3r + 1`. BR(3,r) applied to the actual induced graph on `O(v)` (`induced_regular`) makes every
`x ∈ O(v)` have exactly `r` heads in `O(v)`; out-degree `≥ s` then forces `x` to head all `s - r` members of `M(v)`.
So `O(v)` is an outgoing module of size `s + f ≥ s` with common exterior `M(v) ≠ ∅`, which
`LeanCH.BR.LargeModule.exterior_empty` excludes.

`induced_regular`: if `|M| = qc + 1`, every member of `M` keeps at least `c` heads in `M`, there is no cycle of length
`≤ q` and `BR(q,c)` holds, then every member of `M` has exactly `c` heads (and `c` parents) in `M`. The induced graph
is transported to labels `0, …, qc` as in `LeanCH.BR.ModuleSize.module_size`; BR gives in-degree `c` there, and the
degree sum gives out-degree `c`.
-/

namespace LeanCH.BR.StrictCap

open CH Compose.Boundary Compose.FloorSix

/-- **Induced regularity.** BR(q,c) applied to an actual induced subgraph of order `qc+1` and internal minimum
out-degree `c`: every member has exactly `c` heads inside. -/
theorem induced_regular {G : CH.Digraph} {n q c : Nat} {M : Finset Nat}
    (br : BoundaryRegular q c) (hsub : M ⊆ Finset.range n) (hcard : M.card = q * c + 1)
    (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n q)
    (keep : ∀ x ∈ M, c ≤ (M.filter (fun w => G x w = true)).card) :
    ∀ x ∈ M, (M.filter (fun w => G x w = true)).card = c := by
  classical
  obtain ⟨e, eB, eI, eM, eS⟩ := CH.Side.sc_finset_enumeration hsub
  set m := M.card with hm
  let H : CH.Digraph := fun a b => if a < m then (if b < m then G (e a) (e b) else false) else false
  have hloop : CH.Loopless H m := by
    intro v hv
    change (if v < m then (if v < m then G (e v) (e v) else false) else false) = false
    rw [if_pos hv, if_pos hv]; exact loopless (e v) (eB v hv)
  have hmin : CH.MinOutdegreeAtLeast H m c := by
    intro a ha
    let T : Finset Nat := (Finset.range m).filter (fun i => G (e a) (e i) = true)
    have himage : T.image e = M.filter (fun w => G (e a) w = true) := by
      ext w
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨i, ⟨hi, hG⟩, rfl⟩; exact ⟨eM i hi, hG⟩
      · rintro ⟨hwM, hG⟩; obtain ⟨i, hi, rfl⟩ := eS w hwM; exact ⟨i, ⟨hi, hG⟩, rfl⟩
    have hinj : Set.InjOn e T := by
      intro i hi j hj hij
      have hi' : i ∈ T := hi
      have hj' : j ∈ T := hj
      exact eI i j (Finset.mem_range.mp (Finset.mem_filter.mp hi').1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj').1) hij
    have hTcard : c ≤ T.card := by
      have := Finset.card_image_of_injOn hinj
      rw [himage] at this; rw [← this]; exact keep (e a) (eM a ha)
    refine ⟨(T.sort (· ≤ ·)).take c, ?_, ?_, ?_⟩
    · rw [List.length_take, Finset.length_sort]; omega
    · exact (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)
    · intro w hw
      have hwT : w ∈ T := (Finset.mem_sort _).mp ((List.take_sublist _ _).subset hw)
      simp only [T, Finset.mem_filter, Finset.mem_range] at hwT
      refine ⟨hwT.1, ?_⟩
      change (if a < m then (if w < m then G (e a) (e w) else false) else false) = true
      rw [if_pos ha, if_pos hwT.1]; exact hwT.2
  have hshort : ¬ CH.HasDirectedCycleAtMost H m q := fun h =>
    noShort (CH.Side.sc_induced_subgraph_transport eB eI h)
  rw [hcard] at hloop hmin hshort
  have hreg := br H hloop hmin hshort
  -- every member of M has exactly c parents in M
  have hin : ∀ y ∈ M, (M.filter (fun u => G u y = true)).card = c := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := eS y hy
    have h1 := hreg a (by omega)
    have himage : (par H (q * c + 1) a).image e = M.filter (fun u => G u (e a) = true) := by
      ext w
      simp only [par, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨i, ⟨hi, hG⟩, rfl⟩
        have hi' : i < m := by omega
        have hG' : (if i < m then (if a < m then G (e i) (e a) else false) else false) = true := hG
        rw [if_pos hi', if_pos ha] at hG'
        exact ⟨eM i hi', hG'⟩
      · rintro ⟨hwM, hG⟩
        obtain ⟨i, hi, rfl⟩ := eS w hwM
        refine ⟨i, ⟨by omega, ?_⟩, rfl⟩
        change (if i < m then (if a < m then G (e i) (e a) else false) else false) = true
        rw [if_pos hi, if_pos ha]; exact hG
    have hinj : Set.InjOn e (par H (q * c + 1) a) := by
      intro i hi j hj hij
      have hi' : i ∈ par H (q * c + 1) a := hi
      have hj' : j ∈ par H (q * c + 1) a := hj
      have hi'' := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
      have hj'' := Finset.mem_range.mp (Finset.mem_filter.mp hj').1
      exact eI i j (by omega) (by omega) hij
    rw [← himage, Finset.card_image_of_injOn hinj, h1]
  -- degree sum: every member has exactly c heads in M
  have hsum := Compose.ThinRigid.sum_out_eq_sum_in G M
  have hrhs : ∑ v ∈ M, (M.filter (fun u => G u v = true)).card = ∑ _v ∈ M, c :=
    Finset.sum_congr rfl hin
  have heq : ∑ _x ∈ M, c = ∑ x ∈ M, (M.filter (fun w => G x w = true)).card := by
    rw [hsum, hrhs]
  intro x hx
  exact ((Finset.sum_eq_sum_iff_of_le keep).mp heq x hx).symm

/-- **Strict degree cap (q = 3).** On `3s+1` labels, `s ≥ 2`, with BR(3,t) for all `1 ≤ t < s`, a vertex of
in-degree `s + a ≥ s` and out-degree `s + f` has `3a + 2f + 2 ≤ s`. -/
theorem strict_cap {G : CH.Digraph} {s v : Nat} (hs : 2 ≤ s)
    (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t)
    (loopless : CH.Loopless G (3 * s + 1)) (deg : CH.MinOutdegreeAtLeast G (3 * s + 1) s)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * s + 1) 3) (hv : v < 3 * s + 1)
    (hin : s ≤ (par G (3 * s + 1) v).card) :
    3 * ((par G (3 * s + 1) v).card - s) +
      2 * (((Finset.range (3 * s + 1)).filter (fun w => G v w = true)).card - s) + 2 ≤ s := by
  classical
  have weak := LeanCH.BR.WeakCap.weak_cap (by omega) brs loopless deg noShort hv hin
  have ho_ge : s ≤ ((Finset.range (3 * s + 1)).filter (fun w => G v w = true)).card := out_card deg hv
  have hvI : v ∉ par G (3 * s + 1) v := by simp [par, loopless v hv]
  by_contra hlt
  set I := par G (3 * s + 1) v with hI
  set O := (Finset.range (3 * s + 1)).filter (fun w => G v w = true) with hO
  -- r = a + f, with equality 3a + 2f + 1 = s
  have hr1 : 1 ≤ I.card + O.card - 2 * s := by omega
  have hrs : I.card + O.card - 2 * s < s := by omega
  have hOr : O.card = 3 * (I.card + O.card - 2 * s) + 1 := by omega
  -- K = V \ ({v} ∪ I(v)) and M(v) = K \ O(v)
  have hIsub : insert v I ⊆ Finset.range (3 * s + 1) := by
    intro u hu
    rcases Finset.mem_insert.mp hu with huv | hu
    · rw [huv]; exact Finset.mem_range.mpr hv
    · exact (Finset.mem_filter.mp hu).1
  set K := Finset.range (3 * s + 1) \ insert v I with hK
  have hKcard : K.card = 3 * s + 1 - (I.card + 1) := by
    rw [hK, Finset.card_sdiff_of_subset hIsub, Finset.card_range, Finset.card_insert_of_notMem hvI]
  have hOK : O ⊆ K := by
    intro w hw
    obtain ⟨hwn, hG⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_sdiff.mpr ⟨hwn, ?_⟩
    intro hwI
    rcases Finset.mem_insert.mp hwI with hwv | hwI
    · rw [hwv, loopless v hv] at hG; exact Bool.false_ne_true hG
    · exact no2 loopless noShort hv (Finset.mem_range.mp hwn) hG (Finset.mem_filter.mp hwI).2
  set Mv := K \ O with hMv
  have hMcard : Mv.card = s - (I.card + O.card - 2 * s) := by
    rw [hMv, Finset.card_sdiff_of_subset hOK, hKcard]
    have := Finset.card_le_card hOK
    rw [hKcard] at this
    omega
  -- every head of an out-neighbour of v lies in K
  have headsK : ∀ x ∈ O, ∀ w, w < 3 * s + 1 → G x w = true → w ∈ K := by
    intro x hx w hw hxw
    obtain ⟨hxn', hvx⟩ := Finset.mem_filter.mp hx
    have hxn := Finset.mem_range.mp hxn'
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hw, ?_⟩
    intro hwI
    rcases Finset.mem_insert.mp hwI with hwv | hwI
    · rw [hwv] at hxw; exact no2 loopless noShort hv hxn hvx hxw
    · exact no3 loopless noShort hv hxn hw hvx hxw (Finset.mem_filter.mp hwI).2
  have split : ∀ x ∈ O, ((Finset.range (3 * s + 1)).filter (fun w => G x w = true)).card ≤
      (O.filter (fun w => G x w = true)).card + (Mv.filter (fun w => G x w = true)).card := by
    intro x hx
    have hsub : (Finset.range (3 * s + 1)).filter (fun w => G x w = true) ⊆
        O.filter (fun w => G x w = true) ∪ Mv.filter (fun w => G x w = true) := by
      intro w hw
      obtain ⟨hwn, hxw⟩ := Finset.mem_filter.mp hw
      by_cases hwO : w ∈ O
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwO, hxw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨headsK x hx w (Finset.mem_range.mp hwn) hxw, hwO⟩, hxw⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have keep : ∀ x ∈ O, I.card + O.card - 2 * s ≤ (O.filter (fun w => G x w = true)).card := by
    intro x hx
    have h1 := split x hx
    have h2 := out_card deg (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
    have h3 : (Mv.filter (fun w => G x w = true)).card ≤ Mv.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  have hOsub : O ⊆ Finset.range (3 * s + 1) := Finset.filter_subset _ _
  -- BR(3,r) on the actual induced O(v): exactly r internal heads per row
  have reg := induced_regular (q := 3) (brs _ hr1 hrs) hOsub hOr loopless noShort keep
  -- so every out-neighbour of v heads all of M(v)
  have hcomp : ∀ x ∈ O, ∀ u ∈ Mv, G x u = true := by
    intro x hx u hu
    have h1 := split x hx
    have h2 := out_card deg (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
    have h3 := reg x hx
    have hfull : Mv.filter (fun w => G x w = true) = Mv :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hu' : u ∈ Mv.filter (fun w => G x w = true) := by rw [hfull]; exact hu
    exact (Finset.mem_filter.mp hu').2
  have hmod : ∀ x ∈ O, ∀ w, w < 3 * s + 1 → w ∉ O → G x w = true → w ∈ Mv :=
    fun x hx w hw hwO hxw => Finset.mem_sdiff.mpr ⟨headsK x hx w hw hxw, hwO⟩
  have hMsub : Mv ⊆ Finset.range (3 * s + 1) := fun w hw =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hw).1).1
  have hMO : ∀ u ∈ Mv, u ∉ O := fun u hu => (Finset.mem_sdiff.mp hu).2
  have hempty := LeanCH.BR.LargeModule.exterior_empty hs brs loopless deg noShort hOsub ho_ge
    hMsub hMO hmod hcomp
  rw [hempty, Finset.card_empty] at hMcard
  omega

end LeanCH.BR.StrictCap
