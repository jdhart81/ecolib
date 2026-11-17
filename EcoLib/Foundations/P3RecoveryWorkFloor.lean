import Mathlib

/-!
# A Recovery-Adjusted Work Floor: A Lean Proof that Recovered Supply Lowers, and Exactly Attains, the Fresh-Supply Requirement

`EcoLib.Foundations.P3RecoveryWorkFloor` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `739470d09545`
- `lean/ViridisStatements/P3/RecoveryWorkFloor.lean` (SHA-256 `5f5a53efa57459cf…`)
- `runs/2026-11-17_P3/proofs/P3.RecoveryWorkFloor.lean` (SHA-256 `cc32f316cea84d47…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-17_P3/certification.json`
Engine run: 2026-11-17_P3
Public since: 2026-11-17

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
The Intelligence Bound (dI/dt <= P*D/(k_B T ln 2)) is a conjecture. Theorems here take its physical premise (a Landauer-type cost) as a hypothesis or definition; solving them proves nothing about the conjecture itself.
-/

/-!
# P3 · Recovery-adjusted work floor

Extends `target_requires_supply` of the Useful and Dissipated Work Ledger (canon Run-163,
`series/UDWL/ViridisRun163.lean`, copied as `context/UsefulDissipatedWork.lean`) from two
generic supplies to a *fresh* supply `wf` and a *recovered* supply `wr`.

Model (restated over Mathlib only; same algebra as Run-163 `useful w1 w2 e1 e2` with
`w1 = wf`, `w2 = wr`):
* supplies `wf, wr ≥ 0`;
* modeled conversion efficiencies `ef, er ∈ [0, emax]` with a common cap `emax > 0`;
* useful work `U = ef·wf + er·wr`.

`Statement`:
1. (floor) if `U ≥ T` then `wf ≥ (T - emax·wr) / emax`;
2. (attainment) for every `emax > 0`, `wr ≥ 0` and target `T ≥ emax·wr`, the fresh supply
   `wf = (T - emax·wr)/emax` is nonnegative and, run at `ef = er = emax`, delivers exactly `T`;
   so the floor in part 1 cannot be raised.

`emax` is a bound on *modeled* efficiency. The statement is not a Landauer bound, does not use
the Intelligence Bound, and makes no claim about any real efficiency or recovered supply.
-/

noncomputable section

namespace ViridisStatements.P3.RecoveryWorkFloor

/-- Useful work from fresh supply `wf` at efficiency `ef` and recovered supply `wr` at
efficiency `er`. -/
def useful (wf wr ef er : ℝ) : ℝ := ef * wf + er * wr

/-- The fresh-supply floor `(T - emax·wr) / emax`. -/
def freshFloor (T wr emax : ℝ) : ℝ := (T - emax * wr) / emax

/-- **Proposed sealed target `P3.RecoveryWorkFloor`.** -/
def Statement : Prop :=
  (∀ wf wr ef er emax T : ℝ, 0 ≤ wf → 0 ≤ wr →
    0 ≤ ef → ef ≤ emax → 0 ≤ er → er ≤ emax → 0 < emax →
    T ≤ useful wf wr ef er → freshFloor T wr emax ≤ wf) ∧
  (∀ wr emax T : ℝ, 0 < emax → 0 ≤ wr → emax * wr ≤ T →
    0 ≤ freshFloor T wr emax ∧ useful (freshFloor T wr emax) wr emax emax = T)

/-! ## Sanity checks -/

/-- The Run-163 witness `(w1, w2, e1, e2) = (8, 4, 3/4, 1/2)` read as fresh `8`, recovered `4`:
useful work `8`; with `emax = 3/4` and `T = 8` the floor is `20/3 ≤ 8`. -/
example : useful 8 4 (3/4) (1/2) = 8 ∧ freshFloor 8 4 (3/4) = 20/3 ∧
    freshFloor 8 4 (3/4) ≤ (8 : ℝ) := by
  norm_num [useful, freshFloor]

/-- Attainment witness: `emax = 1/2`, recovered `4`, target `8` give floor `12`, and
`12` units of fresh supply at efficiency `1/2` reach the target exactly. -/
example : freshFloor 8 4 (1/2) = 12 ∧ useful 12 4 (1/2) (1/2) = 8 := by
  norm_num [freshFloor, useful]

/-- Recovery lowers the floor: with no recovered supply the same target needs `16`. -/
example : freshFloor 8 4 (1/2) < freshFloor 8 0 (1/2) := by
  norm_num [freshFloor]

/-- Negative control: fresh supply below the floor (`11 < 12`) cannot reach the target even at
the cap, `useful 11 4 (1/2) (1/2) = 15/2 < 8`. -/
example : useful 11 4 (1/2) (1/2) < 8 := by
  norm_num [useful]

/-- Negative control: the efficiency cap matters. An efficiency `1` above the cap `1/2`
reaches `8` with fresh supply `4`, below the floor `12`. -/
example : useful 4 4 1 1 = 8 ∧ (4 : ℝ) < freshFloor 8 4 (1/2) := by
  norm_num [useful, freshFloor]

/-- Negative control: when recovery alone covers the target (`emax·wr > T`) the floor is
negative, so attainment (part 2) genuinely needs `emax·wr ≤ T`. -/
example : freshFloor 1 4 (1/2) < 0 := by
  norm_num [freshFloor]

end ViridisStatements.P3.RecoveryWorkFloor


namespace ViridisStatements.P3.RecoveryWorkFloor.Proof

open ViridisStatements.P3.RecoveryWorkFloor

/-- Uniform efficiency bound (Run-163 `uniform_efficiency_bound`, restated for the sealed
`useful`): useful work is at most `emax · (wf + wr)`. -/
theorem uniform_efficiency_bound (wf wr ef er emax : ℝ) (hwf : 0 ≤ wf) (hwr : 0 ≤ wr)
    (hef : ef ≤ emax) (her : er ≤ emax) :
    useful wf wr ef er ≤ emax * (wf + wr) := by
  have h1 : 0 ≤ (emax - ef) * wf := mul_nonneg (sub_nonneg.mpr hef) hwf
  have h2 : 0 ≤ (emax - er) * wr := mul_nonneg (sub_nonneg.mpr her) hwr
  unfold useful
  nlinarith

/-- Run-163 `target_requires_supply`, restated: reaching `T` needs total supply `≥ T / emax`. -/
theorem target_requires_supply (wf wr ef er emax T : ℝ) (hwf : 0 ≤ wf) (hwr : 0 ≤ wr)
    (hef : ef ≤ emax) (her : er ≤ emax) (he : 0 < emax) (hT : T ≤ useful wf wr ef er) :
    T / emax ≤ wf + wr := by
  have hu := uniform_efficiency_bound wf wr ef er emax hwf hwr hef her
  rw [div_le_iff₀ he]
  linarith [mul_comm emax (wf + wr)]

/-- The floor is the total-supply bound with the recovered part moved across:
`(T - emax·wr)/emax = T/emax - wr`. -/
theorem freshFloor_eq (T wr emax : ℝ) (he : 0 < emax) :
    freshFloor T wr emax = T / emax - wr := by
  unfold freshFloor
  field_simp

/-- Part 1 (floor). -/
theorem floor (wf wr ef er emax T : ℝ) (hwf : 0 ≤ wf) (hwr : 0 ≤ wr)
    (hef : ef ≤ emax) (her : er ≤ emax) (he : 0 < emax)
    (hT : T ≤ useful wf wr ef er) : freshFloor T wr emax ≤ wf := by
  rw [freshFloor_eq T wr emax he]
  linarith [target_requires_supply wf wr ef er emax T hwf hwr hef her he hT]

/-- Part 2 (attainment): the floor is nonnegative and, at `ef = er = emax`, delivers `T`. -/
theorem attain (wr emax T : ℝ) (he : 0 < emax) (hT : emax * wr ≤ T) :
    0 ≤ freshFloor T wr emax ∧ useful (freshFloor T wr emax) wr emax emax = T := by
  unfold freshFloor useful
  refine ⟨div_nonneg (by linarith) he.le, ?_⟩
  field_simp
  ring

theorem main : ViridisStatements.P3.RecoveryWorkFloor.Statement :=
  ⟨fun wf wr ef er emax T hwf hwr _ hef _ her he hT =>
      floor wf wr ef er emax T hwf hwr hef her he hT,
   fun wr emax T he _ hT => attain wr emax T he hT⟩

end ViridisStatements.P3.RecoveryWorkFloor.Proof
