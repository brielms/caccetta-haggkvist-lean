import LeanCH.BR.BR37Z

/-!
# Boundary regularity `BR(3,7)`, Lean 4.35.0

Paper source: `checkpoints/boundary_20261111/BR37_attempt_subagent.md`, sections 6-7 (audited in
`BR37_audit_subagent.md`).

* `SHyp.theoremE` (**Theorem E**). In a saturated boundary graph at `s = 7` with in-degrees at most 8 and no root
  (`(in, out) = (8, 7)`), every in-degree is at most 7. Then `in ≤ out` everywhere and `Σ in = Σ out`, so
  `in = out` everywhere. At a vertex `u` with `in(u) = out(u) = 8` (`|O| = 8`, `|M| = 5`): `H(u) = ∅`
  (`out(η) ≥ 9 > in(η)`), `K(u) = ∅` (`in_O(x) = out_O(x) + 4` against `|O| = 8`), so every `x ∈ O(u)` misses a row
  and has 3 heads in `O(u)`, which `BR(3,3)` excludes on 8 vertices (`ch_subset`).
* `br_seven`: saturation (`br_of_sat`), Theorem Z (`SHyp.K_nonempty7`), Theorem D (`SHyp.no_root`), Theorem E.
  `BR(3,6)` enters through the strict cap at `s = 7`.
-/

namespace LeanCH.BR.BR37

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of
open LeanCH.BR.BR36

/-- **Theorem E.** -/
theorem SHyp.theoremE {G : CH.Digraph} (H : SHyp 7 G) (noroot : ∀ u, ¬ IsRoot G 7 u) :
    ∀ v, v < 3 * 7 + 1 → ic G (VS 7) v ≤ 7 := by
  classical
  have hle : ∀ v ∈ VS 7, ic G (VS 7) v ≤ oc G (VS 7) v := by
    intro v hv
    have hvn := mem_VS.mp hv
    have h1 := H.cap v hvn
    have h2 := H.out hvn
    by_contra hlt
    exact noroot v ⟨hvn, by omega, by omega⟩
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (Compose.ThinRigid.sum_out_eq_sum_in G (VS 7)).symm
  intro u hu
  by_contra hgt
  have hin : ic G (VS 7) u = 8 := by have := H.cap u hu; omega
  have hout : oc G (VS 7) u = 8 := by rw [← heq u (mem_VS.mpr hu)]; exact hin
  have hMc : (MM G 7 u).card = 5 := by have := H.cM hu; omega
  have cO : (OO G 7 u).card = 8 := by rw [card_OO]; exact hout
  apply ch_subset (q := 3) (c := 3) (S := OO G 7 u) (by norm_num) LeanCH.BR.SmallBR.br_three H.subO
    (Finset.card_pos.mp (by omega)) (by omega) H.loopless H.noShort
  intro x hx
  have miss : ∃ m ∈ MM G 7 u, G x m = false := by
    by_contra hcon
    push Not at hcon
    have hxK : x ∈ KS G 7 u := Finset.mem_filter.mpr ⟨hx, fun m hm => by simpa using hcon m hm⟩
    have hH : (HS G 7 u).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro η hη
      have hηI := HS_sub hη
      have h1 : oc G (VS 7) η = 1 + oc G (II G 7 u) η + oc G (OO G 7 u) η + oc G (MM G 7 u) η :=
        SHyp7.outI H hu hηI
      have h2 : oc G (OO G 7 u) η = 8 := by rw [oc_full (HS_all hη), cO]
      have h3 := H.cap η (H.ltI hηI)
      have h4 := heq η (mem_VS.mpr (H.ltI hηI))
      omega
    have k1 := H.K_in hu hxK
    have k2 := H.K_out hu hxK
    have k3 := oc_ic_le_mem H.loopless H.noShort H.subO hx
    have k4 := heq x (mem_VS.mpr (H.ltO hx))
    have k5 := H.out (H.ltO hx)
    rw [cO] at k3
    omega
  obtain ⟨m, hm, hxm⟩ := miss
  have h1 := H.out (H.ltO hx)
  rw [H.outO hu hx] at h1
  have h2 : oc G (MM G 7 u) x ≤ 4 := by
    rw [← oc_erase_eq (G := G) (A := MM G 7 u) hxm]
    have := oc_le (G := G) ((MM G 7 u).erase m) x
    rw [Finset.card_erase_of_mem hm, hMc] at this
    exact this
  omega

theorem brs7 : ∀ t, 1 ≤ t → t < 7 → BoundaryRegular 3 t := fun t h1 h2 => by
  rcases (by omega : t < 6 ∨ t = 6) with h | rfl
  · exact LeanCH.BR.BR36.brs6 t h1 h
  · exact LeanCH.BR.BR36.br_six

/-- **`BR(3,7)`.** Every loopless digraph on 22 labels with minimum out-degree 7 and no directed cycle of length at
most 3 has every in-degree exactly 7. -/
theorem br_seven : BoundaryRegular 3 7 :=
  br_of_sat (s := 7) (by norm_num) (le_refl _) brs7 (fun _ H _ =>
    SHyp.theoremE H (fun u => H.no_root (fun _ hr _ => SHyp.K_nonempty7 H hr) u))

end LeanCH.BR.BR37
