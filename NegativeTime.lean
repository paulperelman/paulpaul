import ChallengeSpec

/-!
# Negative time in the challenge's public language

This module evaluates the proposed concept of negative time and its
"balance" against the mass gap, inside the repository's public language
(`PublicTheory` + `PublicWilson`, imported through `ChallengeSpec`), without
extra spatial dimensions and without string theory. It is the companion of
`NEGATIVE_TIME_SCENARIOS.md` and the fourth member of the family: `MassGap.lean`
(mass gap: proved but one named axiom node), `Confinement.lean` (confinement:
no datum assumed, unconditional claim not derivable), `Unification.lean`
(unification: ruled out by the decoupled-sector witness; conditional chain
under five named data).

The concept under evaluation: a region of **negative time** whose spectral
weight balances the positive-time weight against the mass gap — an expression
relating the negative component to the gap.

The machine-checked content:

* `NegativeTime` / `negativeShell`: the negative-time region and its shells,
  measurable in the public coordinates.
* `negativeTime_cone_empty`: the negative-time region is **empty inside the
  forward cone** — pure norm bookkeeping on the public coordinates.
* `negativeTime_null`: the spectral weight of the entire negative-time region
  vanishes for **every** state, from `W0.positiveEnergy` alone —
  **unconditionally, without the mass gap**. The invocation of the
  established gap is therefore unnecessary for this verdict: positive energy
  already kills negative time.
* `timeBalance_degenerate`: the proposed balance between the negative and
  positive components degenerates — the negative component is identically
  zero and the positive component equals the total spectral mass, for every
  state and independently of any gap parameter. No expression coupling the
  negative component to the mass gap can survive: its left side is zero.
* `TimeReflects`: the one datum under which negative time could carry
  spectral weight — a time-reflection symmetry intertwining states with the
  spectral PVM (the analogue of the mass-gap module's missing
  `LorentzIntertwines`). It is **not** a datum of the public language.
* `timeReflects_refuted`: this datum is not merely unavailable — it is
  **refuted**: the rest point at time `m > 0` lies in the cone, its image
  under the reflection lies in the cone by `conePreserved` and in negative
  time by `timeImage`, contradicting `negativeTime_cone_empty`. The strong
  (Minkowski time-reversal) formalization of negative time is inconsistent
  with the public language for every theory. The escape route —
  Osterwalder–Schrader reflection on imaginary time — abandons
  `conePreserved` and with it the possibility of any negative-time spectral
  weight in the real-time language; it is conditional on a reflection-
  positivity datum the public API does not contain
  (`NEGATIVE_TIME_SCENARIOS.md`, Part V).

Consequently the negative-time/balance framework is **refuted in its strong
form and conditional-only in its weak form**: the balance degenerates
identically, and the datum that would animate the negative wing is
machine-checkably inconsistent with the language. This file contains no
`sorry` and no `axiom`; nothing is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory Set Function Filter
open scoped Topology NNReal ENNReal

variable {H : HilbertSpace} {Labels : FieldLabels}

/-! ## Geometry copied from the public coordinates -/

/-- The time coordinate as a continuous linear functional. -/
def timeL : Spacetime →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap { toFun := time, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[fun_prop] lemma time_cont : Continuous time := timeL.continuous

/-- The spatial part as a continuous linear map. -/
def spatialL : Spacetime →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap { toFun := spatial, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[fun_prop] lemma spatial_cont : Continuous spatial := spatialL.continuous

@[fun_prop] lemma spatial_norm_cont : Continuous fun p : Spacetime => ‖spatial p‖ :=
  continuous_norm.comp spatial_cont

lemma closed_forwardCone : IsClosed forwardCone :=
  isClosed_le (by fun_prop) time_cont

theorem measurableSet_forwardCone : MeasurableSet forwardCone :=
  closed_forwardCone.measurableSet

@[fun_prop] lemma continuous_minkowskiSquare : Continuous minkowskiSquare := by
  unfold minkowskiSquare; fun_prop

/-! ## The negative-time region -/

/-- The negative-time region: strictly negative time coordinate. -/
def NegativeTime : Set Spacetime := {p : Spacetime | time p < 0}

/-- A negative-time shell: `time ≤ -R` for `R > 0`. -/
def negativeShell (R : ℝ) : Set Spacetime := {p : Spacetime | time p ≤ -R}

theorem measurableSet_negativeTime : MeasurableSet NegativeTime := by
  have h : NegativeTime = {p : Spacetime | 0 ≤ time p}ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, NegativeTime, Set.mem_setOf_eq, not_le]
  rw [h]
  exact (isClosed_le continuous_const time_cont).measurableSet.compl

/-- The negative-time region is empty inside the forward cone: on the cone,
`0 ≤ ‖x‖ ≤ t` forces `t ≥ 0`. -/
theorem negativeTime_cone_empty : forwardCone ∩ NegativeTime = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro p hp
  obtain ⟨hp, ht⟩ := hp
  simp only [forwardCone, Set.mem_setOf_eq] at hp
  simp only [NegativeTime, Set.mem_setOf_eq] at ht
  have hnorm := norm_nonneg (spatial p)
  linarith

/-! ## Spectral nullity of negative time — unconditional -/

/-- The diagonal measure of any state is supported on the closed forward cone
(copied from `MassGap.lean`: `W0.positiveEnergy` + `diagonalIdentity`). -/
theorem diagonal_le_cone (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) (Set.compl forwardCone) = 0 := by
  have hmeas : MeasurableSet (Set.compl forwardCone) := measurableSet_forwardCone.compl
  have h0 : T.energyMomentum.projection (Set.compl forwardCone) = 0 := hW0.positiveEnergy
  have hdi := T.energyMomentum.diagonalIdentity hmeas ψ
  simp only [h0, zero_apply, inner_zero_right] at hdi
  have hreal : (T.energyMomentum.diagonal ψ).real (Set.compl forwardCone) = 0 :=
    Complex.ofReal_eq_zero.mp hdi
  have hne : (T.energyMomentum.diagonal ψ) (Set.compl forwardCone) ≠ ∞ := measure_ne_top _ _
  exact measureReal_eq_zero_iff hne |>.mp hreal

/-- **The spectral weight of negative time vanishes for every state.**
The negative-time region lies inside the cone complement, and positive
energy (`W0`, the weakest public datum) nullifies the complement. No mass
gap is invoked: the verdict precedes and survives without the established
gap. -/
theorem negativeTime_null (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) NegativeTime = 0 := by
  have hsub : NegativeTime ⊆ Set.compl forwardCone := by
    intro p hp
    simp only [NegativeTime, Set.mem_setOf_eq] at hp
    intro hc
    simp only [forwardCone, Set.mem_setOf_eq] at hc
    have hnorm := norm_nonneg (spatial p)
    linarith
  exact le_antisymm ((measure_mono hsub).trans (le_of_eq (diagonal_le_cone T hW0 ψ))) zero_le

/-- Every negative-time shell is spectrally null. -/
theorem negativeShell_null (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier)
    {R : ℝ} (hR : 0 < R) : (T.energyMomentum.diagonal ψ) (negativeShell R) = 0 := by
  have hsub : negativeShell R ⊆ NegativeTime := by
    intro p hp
    simp only [negativeShell, Set.mem_setOf_eq] at hp
    simp only [NegativeTime, Set.mem_setOf_eq]
    linarith
  exact le_antisymm ((measure_mono hsub).trans (le_of_eq (negativeTime_null T hW0 ψ))) zero_le

/-! ## The balance: degenerate, gap-independent -/

/-- **The proposed balance degenerates.** The negative component of the
spectral weight is identically zero, and the positive component `{0 ≤ t}`
carries the entire mass: the balance
`μ_ψ{0 ≤ t} − μ_ψ{t < 0} = μ_ψ(ℝ⁴)` holds for every state and is
independent of any mass-gap parameter. Any expression coupling the negative
component to the gap balances against zero. -/
theorem timeBalance_degenerate (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) NegativeTime = 0 ∧
    (T.energyMomentum.diagonal ψ) {p : Spacetime | 0 ≤ time p} =
      (T.energyMomentum.diagonal ψ) Set.univ := by
  refine ⟨negativeTime_null T hW0 ψ, ?_⟩
  have hcomp : {p : Spacetime | 0 ≤ time p} = NegativeTimeᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, NegativeTime, Set.mem_setOf_eq, not_lt]
  rw [hcomp]
  have hadd := measure_add_measure_compl measurableSet_negativeTime (μ := T.energyMomentum.diagonal ψ)
  rw [negativeTime_null T hW0 ψ, zero_add] at hadd
  exact hadd

/-! ## The rest point — the positive wing's anchor -/

/-- The rest point at energy `m > 0`: zero spatial momentum, `t = m`
(copied from `MassGap.lean`'s witness, cone-membership and time coordinate
only). -/
theorem rest_point_core {m : ℝ} (hpos : 0 < m) :
    (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) ∈ forwardCone ∧
    time (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) = m := by
  have hz : ∀ i : SpaceAxis,
      (Pi.single (M := fun _ : Axis => ℝ) timeAxis m) i.castSucc = 0 :=
    fun i => Pi.single_eq_of_ne (M := fun _ : Axis => ℝ) (Fin.castSucc_ne_last i) m
  have hco : WithLp.ofLp (spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m))) = 0 :=
    funext fun i => hz i
  have hsz : spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) = 0 := by
    rw [← WithLp.toLp_ofLp (p := (2 : ℝ≥0∞))
      (x := spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)))]
    rw [hco, WithLp.toLp_zero]
  have hnorm : ‖spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m))‖ = 0 :=
    norm_eq_zero.mpr hsz
  have htime : time (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) = m := by
    show (WithLp.ofLp (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m))) timeAxis = m
    rw [WithLp.ofLp_toLp]
    exact Pi.single_eq_same (M := fun _ : Axis => ℝ) timeAxis m
  have hcone : (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) ∈ forwardCone := by
    simp only [forwardCone, Set.mem_setOf_eq]
    rw [hnorm, htime]
    exact hpos.le
  exact ⟨hcone, htime⟩

/-! ## The one datum that could animate the negative wing — and its refutation -/

/-- The candidate time-reflection datum — the one structure under which
negative time could carry spectral weight: an involutive time reflection
acting on states, intertwined with the energy-momentum PVM, preserving the
cone. This is the strong (Minkowski time-reversal) formalization; it is the
analogue of the mass-gap module's missing `LorentzIntertwines`. No structure
field of `PublicTheory` carries any of it. -/
structure TimeReflects (T : WightmanTheory H Labels) where
  reflect : Spacetime →L[ℝ] Spacetime
  timeImage (p : Spacetime) : time (reflect p) = - time p
  conePreserved (p : Spacetime) : p ∈ forwardCone ↔ reflect p ∈ forwardCone
  onStates : H.Operator
  vacuumFixed : onStates T.fields.vacuum.1 = T.fields.vacuum.1
  domainMapsTo (v : H.carrier) : v ∈ T.fields.domain → onStates v ∈ T.fields.domain
  spectralCovariance {A : Set Spacetime} (_ : MeasurableSet A) :
    T.energyMomentum.projection (Set.preimage (reflect : Spacetime → Spacetime) A) =
      (onStates.adjoint).comp ((T.energyMomentum.projection A).comp onStates)

/-- **The strong negative-time datum is refuted.** For every `m > 0` the rest
point at energy `m` lies in the cone; `conePreserved` keeps its reflection in
the cone; `timeImage` puts that image at time `-m < 0`, inside the negative
region — but the cone's intersection with negative time is empty. The datum
is inconsistent with the public language for every theory: the negative wing
cannot be animated by a Minkowski time-reflection symmetry, because positive
energy forbids such a symmetry to begin with. -/
theorem timeReflects_refuted (T : WightmanTheory H Labels) {m : ℝ} (hpos : 0 < m)
    (D : TimeReflects T) : False := by
  obtain ⟨hcone, htime⟩ := rest_point_core (m := m) hpos
  set p₀ := WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m) with hp₀
  have h1 : D.reflect p₀ ∈ forwardCone := (D.conePreserved p₀).mp hcone
  have h2 : D.reflect p₀ ∈ NegativeTime := by
    simp only [NegativeTime, Set.mem_setOf_eq]
    rw [D.timeImage p₀, htime]
    exact neg_lt_zero.mpr hpos
  have hmem : D.reflect p₀ ∈ forwardCone ∩ NegativeTime := Set.mem_inter h1 h2
  rw [negativeTime_cone_empty, Set.mem_empty_iff_false] at hmem
  exact hmem.elim

/-! ## The pullback law — what the (refuted) datum would have yielded -/

/-- The pullback law: spectral pairings transfer across the reflection
(copied from `Unification.lean`'s `diagonal_pullback`, proved from PVM
algebra alone given the datum). Vacuous in the strong form — the datum is
refuted above — but it is exactly the identity the weak (Osterwalder–Schrader
imaginary-time) formalization would have to replace with a reflection-
positivity interface the public API does not contain. -/
theorem diagonal_pullback_reflect (T : WightmanTheory H Labels) (D : TimeReflects T)
    {A : Set Spacetime} (hA : MeasurableSet A) (ψ : H.carrier) :
    inner ℂ (D.onStates ψ) ((T.energyMomentum.projection A) ((D.onStates) ψ)) =
      inner ℂ ψ ((T.energyMomentum.projection
        (Set.preimage (D.reflect : Spacetime → Spacetime) A)) ψ) := by
  have h1 : inner ℂ (D.onStates ψ) ((T.energyMomentum.projection A) ((D.onStates) ψ))
      = inner ℂ ψ ((D.onStates).adjoint ((T.energyMomentum.projection A) ((D.onStates) ψ))) :=
    (ContinuousLinearMap.adjoint_inner_right (D.onStates) ψ _).symm
  have h2 : ((D.onStates).adjoint) ((T.energyMomentum.projection A) ((D.onStates) ψ))
      = (((D.onStates).adjoint).comp ((T.energyMomentum.projection A).comp (D.onStates))) ψ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [h1, h2, ← D.spectralCovariance hA]

end YangMills
end
