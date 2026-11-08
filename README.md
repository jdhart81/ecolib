# EcoLib

EcoLib is a Lean 4 library of machine-checked results from Viridis conservation science, built on Mathlib. Version 0.1.0 holds 135 modules and 1643 theorems. A daily job adds newly certified results after checking each one in a network-less sandbox.

The [Eco-Lean Bench](https://huggingface.co/datasets/viridis-research/eco-lean-bench) is the companion AI benchmark (the same kind of results with the proofs removed). EcoLib is the library you import: the proofs themselves.

## Use it

In your `lakefile.toml`:

```toml
[[require]]
name = "ecolib"
git = "https://github.com/jdhart81/ecolib"
rev = "v0.1.0"
```

Then `import EcoLib` for everything, or one module, for example `import EcoLib.Alignment.CertificationComplexity`. EcoLib pins Lean `v4.28.0` and Mathlib `8f9d9cff6bd7`; run `lake exe cache get` before building.

## What is checked

Every module passed, at the pinned toolchain and Mathlib:

1. **Source rules:** no `sorry`, `axiom`, `native_decide`, `unsafe`, custom syntax or other escape hatches.
2. **Compiles:** under its EcoLib name, against Mathlib and its own EcoLib dependencies only.
3. **Axiom audit:** Lean lists every constant the module declares; each depends only on `propext`, `Quot.sound` and `Classical.choice`.
4. **Kernel replay:** `leanchecker` replays every declaration.
5. **One environment:** the root module `EcoLib` imports every module and compiles.

This repository's CI repeats the build and the axiom audit on every push.

## What it does not claim

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.

Empirical-validation status is in each module's doc comment and in `provenance/modules.json`.

Compiling here does not raise a result's status. The canon's [claims matrix](https://github.com/jdhart81/viridis-canon/blob/main/CLAIMS_MATRIX.md) labels headline results Derived, Conditional, Definition-expansion, Bridge-assumption or Conjecture; read it before citing one. Results the canon marks Exploratory (quarantined) are not in EcoLib.

The Intelligence Bound (dI/dt <= P*D/(k_B T ln 2)) is a conjecture. Theorems here take its physical premise (a Landauer-type cost) as a hypothesis or definition; solving them proves nothing about the conjecture itself. Modules that mention it say so in their doc comment.

## Modules

| Domain | Modules | Theorems |
|---|---:|---:|
| The Intelligence Bound and information-rate limits (conjecture-conditional) (`EcoLib.IntelligenceBound`) | 14 | 108 |
| D-Score parcel scoring and ranking (`EcoLib.DScore`) | 5 | 41 |
| Habitat corridors and HDFM forest management (`EcoLib.Corridors`) | 12 | 145 |
| Restoration, afforestation and ecological succession (`EcoLib.Restoration`) | 19 | 252 |
| Thermodynamic economics, prices and allocation (`EcoLib.Economics`) | 11 | 79 |
| Monitoring, detection and early warning (`EcoLib.Monitoring`) | 6 | 119 |
| Learning, cognition and attention (`EcoLib.Learning`) | 16 | 165 |
| Alignment, verification and safety of decision systems (`EcoLib.Alignment`) | 15 | 437 |
| Ecosystem services, mutualism and Gaian systems (`EcoLib.Ecosystems`) | 18 | 143 |
| Thermodynamic speed limits and dissipation (`EcoLib.Thermodynamics`) | 14 | 123 |
| Combinatorial and analytic foundations (`EcoLib.Foundations`) | 5 | 31 |

### The Intelligence Bound and information-rate limits (conjecture-conditional)

- `EcoLib.IntelligenceBound.Core` (conjecture-conditional). 22 theorems; source jdhart81/viridis-canon P0_IntelligenceBound/Current.lean.
- `EcoLib.IntelligenceBound.DutyCycleLedger` (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon Run-147.
- `EcoLib.IntelligenceBound.FixedOverheadEnergy`. 7 theorems; source jdhart81/viridis-canon Run-178.
- `EcoLib.IntelligenceBound.Impossibility`: Conservation feasibility — corrigibility rate ceiling, conditional on the Intelligence Bound premises (conjecture-conditional). 8 theorems; source jdhart81/viridis-canon P3_Impossibility.lean.
- `EcoLib.IntelligenceBound.SLSPTIntelligenceBound`: Inverse-square shadow-price and capacity planner. 5 theorems; source jdhart81/viridis-canon P5_SLSPT/IntelligenceBound.lean.
- `EcoLib.IntelligenceBound.SLSPTInverseSquare`: Inverse-square shadow-price and capacity planner. 5 theorems; source jdhart81/viridis-canon P5_SLSPT/InverseSquare.lean.
- `EcoLib.IntelligenceBound.SLSPTShadowPrice`: Inverse-square shadow-price and capacity planner. 4 theorems; source jdhart81/viridis-canon P5_SLSPT/ShadowPrice.lean.
- `EcoLib.IntelligenceBound.SLSPTShadowPriceLevelCurves`: Inverse-square shadow-price and capacity planner. 5 theorems; source jdhart81/viridis-canon P5_SLSPT/ShadowPriceLevelCurves.lean.
- `EcoLib.IntelligenceBound.SLSPTTowerOrdering`: Inverse-square shadow-price and capacity planner. 5 theorems; source jdhart81/viridis-canon P5_SLSPT/SLSPTTowerOrdering.lean.
- `EcoLib.IntelligenceBound.SequentialAlignmentRetention`. 8 theorems; source jdhart81/viridis-canon Run-162.
- `EcoLib.IntelligenceBound.SymbioticAccounting`: The Symbiotic Accounting Certificate: Complementarity Does Not Create Thermodynamic Capacity (conjecture-conditional). 10 theorems; source jdhart81/viridis-canon Run-137.
- `EcoLib.IntelligenceBound.SymbioticIntelligenceBound`: Symbiotic reciprocity and surplus audit (conjecture-conditional). 5 theorems; source jdhart81/viridis-canon SymbioticIntelligenceBound.lean.
- `EcoLib.IntelligenceBound.SymbioticTransferThreshold` (conjecture-conditional). 10 theorems; source jdhart81/viridis-canon Run-157.
- `EcoLib.IntelligenceBound.ThermodynamicEconomics`: Thermodynamic economics — production bound P·D/(k_B·T·ln 2), conditional on the Intelligence Bound premises (conjecture-conditional). 8 theorems; source jdhart81/viridis-canon P4_ThermodynamicEconomics.lean.

### D-Score parcel scoring and ranking

- `EcoLib.DScore.DScore`. 2 theorems; source jdhart81/viridis-canon P1_DScore.lean.
- `EcoLib.DScore.MeasurementEnergyCeiling`. 5 theorems; source jdhart81/viridis-canon Run-175.
- `EcoLib.DScore.SnapshotAlignment`. 13 theorems; source jdhart81/viridis-canon releases/2026-08-08/The_D-Score_Snapshot_Alignment_Theorem/lean/SnapshotAlignment.lean.
- `EcoLib.DScore.StewardshipUncertaintyReserve`. 10 theorems; source jdhart81/viridis-canon Run-160.
- `EcoLib.DScore.WeightCharter`: D-Score robustness — does a parcel ranking survive disputed weights. 11 theorems; source jdhart81/viridis-canon Run-132.

### Habitat corridors and HDFM forest management

- `EcoLib.Corridors.BilateralBenefitReciprocityCorridor`: Bilateral-benefit reciprocity corridor. 16 theorems; source jdhart81/viridis-canon Run-128.
- `EcoLib.Corridors.CorridorOverlapDuality`: The Corridor Overlap Duality Certificate: An exact synchrony-diversification tradeoff for two shared habitat paths. 6 theorems; source jdhart81/viridis-canon Run-133.
- `EcoLib.Corridors.CorridorPriority`: Corridor priority — which corridor link to protect first. 38 theorems; source jdhart81/viridis-canon Run-124.
- `EcoLib.Corridors.CorridorStewardship`. 6 theorems; source jdhart81/viridis-canon series/CorridorStewardship.lean.
- `EcoLib.Corridors.DualCorridor`. 20 theorems; source jdhart81/viridis-canon series/DualCorridor.lean.
- `EcoLib.Corridors.HDFMPOC`: HDFM — corridor width is monotone in Strahler order. 8 theorems; source jdhart81/viridis-canon P2_HDFM_POC.lean.
- `EcoLib.Corridors.PerennialCorridor`: Perennial corridor — holding power grows with decay rate (conjecture-conditional). 15 theorems; source jdhart81/viridis-canon PerennialCorridor.lean.
- `EcoLib.Corridors.ReciprocalCorridorBottleneck`. 9 theorems; source jdhart81/viridis-canon Run-161.
- `EcoLib.Corridors.SharedCorridorFootprint`. 6 theorems; source jdhart81/viridis-canon Run-173.
- `EcoLib.Corridors.SymbioticCorridor`. 9 theorems; source jdhart81/viridis-canon series/SymbioticCorridor.lean.
- `EcoLib.Corridors.TwoRouteStewardship`. 8 theorems; source jdhart81/viridis-canon Run-152.
- `EcoLib.Corridors.WuWeiCorridor`. 4 theorems; source jdhart81/viridis-canon series/WuWeiCorridor.lean.

### Restoration, afforestation and ecological succession

- `EcoLib.Restoration.AfforestationStewardship`: Afforestation — seeding efficiency and the 8× edge-hostility lever (conjecture-conditional). 5 theorems; source jdhart81/viridis-canon series/AfforestationStewardship.lean.
- `EcoLib.Restoration.CarbonContinuity`: Carbon Continuity — wildfire recovery threshold diagnostic. 6 theorems; source jdhart81/viridis-canon releases/2026-08-08/Carbon_Continuity_After_Wildfire/lean/CarbonContinuity.lean.
- `EcoLib.Restoration.EcopoieticHedge`. 6 theorems; source jdhart81/viridis-canon releases/2026-08-08/The_Ecopoietic_Hedge/lean/EcopoieticHedge.lean.
- `EcoLib.Restoration.EcopoieticOrdering`. 28 theorems; source jdhart81/viridis-canon series/EcopoieticOrdering.lean.
- `EcoLib.Restoration.EcopoieticSuccession` (conjecture-conditional). 11 theorems; source jdhart81/viridis-canon series/EcopoieticSuccession.lean.
- `EcoLib.Restoration.ForestNucleation`: Restoration — nucleation planting design (critical cluster size n* + go/no-go). 4 theorems; source jdhart81/viridis-canon series/ForestNucleation.lean.
- `EcoLib.Restoration.FragmentationHysteresis` (conjecture-conditional). 30 theorems; source jdhart81/viridis-canon series/FragmentationHysteresis.lean.
- `EcoLib.Restoration.MutualistCoestablishment` (conjecture-conditional). 15 theorems; source jdhart81/viridis-canon series/MutualistCoestablishment.lean.
- `EcoLib.Restoration.P2Afforestation`: Re-certifying the Viridis OS Decision Kernels: A Lean Proof of the Afforestation Seeding Core. 3 theorems; source jdhart81/viridis-research 2026-11-01_P2.
- `EcoLib.Restoration.P2CarbonContinuity`: Re-certifying the Carbon Continuity Threshold: A Lean Proof of the Two-Pool Regenerative Coupling Condition under a Pinned Toolchain. 3 theorems; source jdhart81/viridis-research 2026-10-29_P2.
- `EcoLib.Restoration.P2Restoration`: Re-certifying the Viridis OS Decision Kernels: A Lean Proof of the Restoration Critical-Nucleus Core. 6 theorems; source jdhart81/viridis-research 2026-10-31_P2.
- `EcoLib.Restoration.PlasmaNFixEnergy`. 14 theorems; source jdhart81/viridis-canon P7_PlasmaNFix/Energy.lean.
- `EcoLib.Restoration.PlasmaNFixFoundations`: Plasma N-fixation — information-rate bound structure. 8 theorems; source jdhart81/viridis-canon P7_PlasmaNFix/Foundations.lean.
- `EcoLib.Restoration.PlasmaNFixIntegration`: Plasma N-fixation — information-rate bound structure. 19 theorems; source jdhart81/viridis-canon P7_PlasmaNFix/Integration.lean.
- `EcoLib.Restoration.SeedSourceBottleneckCertificate`: Seed-source bottleneck certificate. 65 theorems; source jdhart81/viridis-canon Run-130.
- `EcoLib.Restoration.SharedFacilitation`. 6 theorems; source jdhart81/viridis-canon Run-149.
- `EcoLib.Restoration.StewardshipOptionReserve`. 6 theorems; source jdhart81/viridis-canon Run-140.
- `EcoLib.Restoration.UniversalNucleationMetaTheorem`. 8 theorems; source jdhart81/viridis-canon series/UniversalNucleationMetaTheorem.lean.
- `EcoLib.Restoration.UsefulDissipatedWork`. 9 theorems; source jdhart81/viridis-canon Run-163.

### Thermodynamic economics, prices and allocation

- `EcoLib.Economics.CapacityHarmonization` (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon series/CapacityHarmonization.lean.
- `EcoLib.Economics.DualPriceAlignment`. 6 theorems; source jdhart81/viridis-canon Run-150.
- `EcoLib.Economics.HarmonicValuation`. 3 theorems; source jdhart81/viridis-canon series/HarmonicValuation.lean.
- `EcoLib.Economics.P2Harmonization`: Re-certifying the Viridis OS Decision Kernels: A Lean Proof of the Harmonization Scalar-Price Welfare Core. 7 theorems; source jdhart81/viridis-research 2026-11-02_P2.
- `EcoLib.Economics.RetrofitWaterFilling`: Ecological-thermodynamic capital allocation. 6 theorems; source jdhart81/viridis-canon Run-139.
- `EcoLib.Economics.StewardshipReserve`. 4 theorems; source jdhart81/viridis-canon Run-172.
- `EcoLib.Economics.StewardshipSetpoint`: Stewardship setpoint — which way to move capacity toward D* (conjecture-conditional). 13 theorems; source jdhart81/viridis-canon StewardshipSetpoint.lean.
- `EcoLib.Economics.SwitchingDissipationPayback`. 11 theorems; source jdhart81/viridis-canon Run-159.
- `EcoLib.Economics.SymbioticRiskPremium`: Mutualist — natural-capital risk-premium pricing (conjecture-conditional). 9 theorems; source jdhart81/viridis-canon series/SymbioticRiskPremium.lean.
- `EcoLib.Economics.ThermodynamicDiscounting` (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon series/ThermodynamicDiscounting.lean.
- `EcoLib.Economics.UniversalWaterfilling`: Universal water-filling — the equimarginal split is optimal (conjecture-conditional). 8 theorems; source jdhart81/viridis-canon UniversalWaterfilling.lean.

### Monitoring, detection and early warning

- `EcoLib.Monitoring.AnytimeMonitoringChangeCertificate`: Anytime monitoring change certificate. 77 theorems; source jdhart81/viridis-canon Run-129.
- `EcoLib.Monitoring.FreshnessReserve`. 6 theorems; source jdhart81/viridis-canon Run-148.
- `EcoLib.Monitoring.HarmonicEarlyWarning`. 11 theorems; source jdhart81/viridis-canon series/HarmonicEarlyWarning.lean.
- `EcoLib.Monitoring.PairedDetectorCoverage`. 7 theorems; source jdhart81/viridis-canon Run-165.
- `EcoLib.Monitoring.StewardshipRevisit`. 8 theorems; source jdhart81/viridis-canon series/StewardshipRevisit.lean.
- `EcoLib.Monitoring.WuWeiSampling`. 10 theorems; source jdhart81/viridis-canon series/WuWeiSampling.lean.

### Learning, cognition and attention

- `EcoLib.Learning.BoundedMemoryLearning`: Bounded-memory learning — erasure dissipation floor (conjecture-conditional). 4 theorems; source jdhart81/viridis-canon BoundedMemoryLearning.lean.
- `EcoLib.Learning.CognitiveSwitchingHysteresis`: Directional switching hysteresis certificate. 6 theorems; source jdhart81/viridis-canon Run-131.
- `EcoLib.Learning.CognitiveThroughput` (conjecture-conditional). 5 theorems; source jdhart81/viridis-canon series/S6_CognitionLearning/CognitiveThroughput.lean.
- `EcoLib.Learning.DissipativeGeneralization` (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon series/DissipativeGeneralization.lean.
- `EcoLib.Learning.FreeEnergyFloorHabitable`: A Free-Energy Floor for Habitable-State Concentration: A Coarse-Grained Relative-Entropy Audit for Gaian Models. 7 theorems; source jdhart81/viridis-canon Run-123.
- `EcoLib.Learning.GrokkingNucleation` (conjecture-conditional). 5 theorems; source jdhart81/viridis-canon series/GrokkingNucleation.lean.
- `EcoLib.Learning.HarmonizedDescent` (conjecture-conditional). 4 theorems; source jdhart81/viridis-canon series/S6_CognitionLearning/HarmonizedDescent.lean.
- `EcoLib.Learning.InformationSymbiosisBalance`: Information Symbiosis Balance: A Conditional-Dependence Criterion for Cooperative Learning. 63 theorems; source jdhart81/viridis-canon Run-121.
- `EcoLib.Learning.MELT` (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon series/MELT.lean.
- `EcoLib.Learning.PlasticityVitrification`. 9 theorems; source jdhart81/viridis-canon series/PlasticityVitrification.lean.
- `EcoLib.Learning.ReciprocalDistillationAccounting`. 6 theorems; source jdhart81/viridis-canon Run-176.
- `EcoLib.Learning.RelativeEntropyChangeBudget`. 9 theorems; source jdhart81/viridis-canon Run-164.
- `EcoLib.Learning.RetentionFloor`. 8 theorems; source jdhart81/viridis-canon Run-136.
- `EcoLib.Learning.SignedBiasCancellation`. 8 theorems; source jdhart81/viridis-canon Run-154.
- `EcoLib.Learning.ThermalStepCorridor`. 7 theorems; source jdhart81/viridis-canon Run-151.
- `EcoLib.Learning.ThermodynamicAttention`: Thermodynamic attention — slower modes are filled first (conjecture-conditional). 12 theorems; source jdhart81/viridis-canon ThermodynamicAttention.lean.

### Alignment, verification and safety of decision systems

- `EcoLib.Alignment.CertificationComplexity` (conjecture-conditional). 3 theorems; source jdhart81/viridis-canon series/CertificationComplexity.lean.
- `EcoLib.Alignment.CheckerAgreement`. 4 theorems; source jdhart81/viridis-canon Run-166.
- `EcoLib.Alignment.ConjunctiveAuditStewardshipTheorem`: The Conjunctive Audit Stewardship Theorem: Why Evidence Portfolios Reward Bundles Rather Than Scattered Greedy Checks. 59 theorems; source jdhart81/viridis-canon Run-120.
- `EcoLib.Alignment.DecoherentSelection`: Decoherent selection — ambiguity cost is at most ln N (conjecture-conditional). 12 theorems; source jdhart81/viridis-canon DecoherentSelection.lean.
- `EcoLib.Alignment.DeferenceReserveEqualization`. 9 theorems; source jdhart81/viridis-canon Run-158.
- `EcoLib.Alignment.EffortlessEquilibrium`: Effortless equilibrium — forcing-time floor, conditional on the Intelligence Bound premises (conjecture-conditional). 11 theorems; source jdhart81/viridis-canon EffortlessEquilibrium.lean.
- `EcoLib.Alignment.ForbiddenProxyInformationCapacity`: Forbidden-proxy information capacity audit. 109 theorems; source jdhart81/viridis-canon Run-126.
- `EcoLib.Alignment.MRAB`: Multi-ring alignment capacity audit (conjecture-conditional). 10 theorems; source jdhart81/viridis-canon MRAB.lean.
- `EcoLib.Alignment.ManipulationProofWeighting` (conjecture-conditional). 7 theorems; source jdhart81/viridis-canon series/ManipulationProofWeighting.lean.
- `EcoLib.Alignment.MomentRobustPrecautionaryCapacity`: Moment-robust precautionary capacity certificate. 47 theorems; source jdhart81/viridis-canon Run-127.
- `EcoLib.Alignment.ReviewChecks`. 19 theorems; source jdhart81/viridis-canon releases/2026-08-08/Robustness_Before_Performance/lean/ReviewChecks.lean.
- `EcoLib.Alignment.RobustnessKernelV1`. 27 theorems; source jdhart81/viridis-canon releases/2026-08-08/Robustness_Before_Performance/lean/RobustnessKernelV1.lean.
- `EcoLib.Alignment.SharedChannelCoverageAudit`: Shared-channel coverage audit. 54 theorems; source jdhart81/viridis-canon Run-125.
- `EcoLib.Alignment.SufficientSanitization`: The Sufficient Sanitization Certificate: Task Information, Data Minimization, and an Ideal Erasure Gap. 5 theorems; source jdhart81/viridis-canon Run-135.
- `EcoLib.Alignment.ZenoAlignmentBudget`: The Zeno Alignment Budget: Uniform Projective Steps and a Noise-Limited Measurement Count. 61 theorems; source jdhart81/viridis-canon Run-122.

### Ecosystem services, mutualism and Gaian systems

- `EcoLib.Ecosystems.AlignmentCone`: The Gaian Alignment Cone Certificate: When Local Directional Bounds Survive Aggregation. 9 theorems; source jdhart81/viridis-canon Run-138.
- `EcoLib.Ecosystems.BiosphereErasureBound`: Biosphere erasure floor — total erasure cost is at least N·ε_L (conjecture-conditional). 5 theorems; source jdhart81/viridis-canon BiosphereErasureBound.lean.
- `EcoLib.Ecosystems.BiosphereProductivity` (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon Bridge_BiosphereProductivity.lean.
- `EcoLib.Ecosystems.ConservationOperator` (conjecture-conditional). 7 theorems; source jdhart81/viridis-canon ConservationOperator.lean.
- `EcoLib.Ecosystems.DendriticCorridor`. 7 theorems; source jdhart81/viridis-canon EcoChain_DendriticCorridor.lean.
- `EcoLib.Ecosystems.EcoChainInstrument` (conjecture-conditional). 4 theorems; source jdhart81/viridis-canon Bridge_EcoChainInstrument.lean.
- `EcoLib.Ecosystems.GaianHarmonization`: Harmonization — single-price coordination toward a shared target (conjecture-conditional). 10 theorems; source jdhart81/viridis-canon series/GaianHarmonization.lean.
- `EcoLib.Ecosystems.GaianMutualismSelection` (conjecture-conditional). 15 theorems; source jdhart81/viridis-canon series/GaianMutualismSelection.lean.
- `EcoLib.Ecosystems.JointMinimumFloor`. 5 theorems; source jdhart81/viridis-canon Run-174.
- `EcoLib.Ecosystems.KSCT`. 4 theorems; source jdhart81/viridis-canon series/KSCT.lean.
- `EcoLib.Ecosystems.MutualisticAttestation`: Mutualistic attestation — attester throughput speed limit. 19 theorems; source jdhart81/viridis-canon MutualisticAttestation.lean.
- `EcoLib.Ecosystems.MutualisticInference` (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon series/MutualisticInference.lean.
- `EcoLib.Ecosystems.ReciprocalRescue`. 7 theorems; source jdhart81/viridis-canon Run-153.
- `EcoLib.Ecosystems.ResponseAdjustedAlignment`. 5 theorems; source jdhart81/viridis-canon series/RAAC/ResponseAdjustedAlignment.lean.
- `EcoLib.Ecosystems.SharedVerificationOverhead`. 8 theorems; source jdhart81/viridis-canon Run-155.
- `EcoLib.Ecosystems.SinglePartnerLossReserve`. 8 theorems; source jdhart81/viridis-canon Run-169.
- `EcoLib.Ecosystems.SymbioticSpeedLimit` (conjecture-conditional). 10 theorems; source jdhart81/viridis-canon series/SymbioticSpeedLimit.lean.
- `EcoLib.Ecosystems.VerificationPhaseTransition` (conjecture-conditional). 8 theorems; source jdhart81/viridis-canon series/VerificationPhaseTransition.lean.

### Thermodynamic speed limits and dissipation

- `EcoLib.Thermodynamics.BoundedMemoryDissipation`. 5 theorems; source jdhart81/viridis-canon BoundedMemoryDissipation.lean.
- `EcoLib.Thermodynamics.DeadlineCarnot`. 17 theorems; source jdhart81/viridis-canon series/DeadlineCarnot.lean.
- `EcoLib.Thermodynamics.GeodesicSaturation`: Geodesic saturation — forcing excess splits into speed and path excess (conjecture-conditional). 6 theorems; source jdhart81/viridis-canon GeodesicSaturation.lean.
- `EcoLib.Thermodynamics.HeatAndDisorder` (conjecture-conditional). 12 theorems; source jdhart81/viridis-canon Book_HeatAndDisorder.lean.
- `EcoLib.Thermodynamics.IntelligenceExergy`. 6 theorems; source jdhart81/viridis-canon series/IntelligenceExergy.lean.
- `EcoLib.Thermodynamics.KibbleZurekSpeedLimit` (conjecture-conditional). 8 theorems; source jdhart81/viridis-canon series/KibbleZurekSpeedLimit.lean.
- `EcoLib.Thermodynamics.MonitoringResponseReserve`. 9 theorems; source jdhart81/viridis-canon Run-156.
- `EcoLib.Thermodynamics.PSITSymplectic` (conjecture-conditional). 8 theorems; source jdhart81/viridis-canon PSIT_Symplectic.lean.
- `EcoLib.Thermodynamics.ReservedActivity`. 4 theorems; source jdhart81/viridis-canon Run-171.
- `EcoLib.Thermodynamics.SchedulerFreeEnergy`. 6 theorems; source jdhart81/viridis-canon releases/2026-08-08/The_Scheduler_Free-Energy_Certificate/lean/SchedulerFreeEnergy.lean.
- `EcoLib.Thermodynamics.SymbioticEqualization`. 7 theorems; source jdhart81/viridis-canon series/SESL/SymbioticEqualization.lean.
- `EcoLib.Thermodynamics.WuWeiCrypticity` (conjecture-conditional). 8 theorems; source jdhart81/viridis-canon series/WuWeiCrypticity.lean.
- `EcoLib.Thermodynamics.WuWeiDominance`. 13 theorems; source jdhart81/viridis-canon series/WuWeiDominance.lean.
- `EcoLib.Thermodynamics.WuWeiInference`. 14 theorems; source jdhart81/viridis-canon series/WuWeiInference.lean.

### Combinatorial and analytic foundations

- `EcoLib.Foundations.KZSLTReprove`. 10 theorems; source jdhart81/viridis-canon series/KZSLTReprove.lean.
- `EcoLib.Foundations.MIST`. 5 theorems; source jdhart81/viridis-canon series/MIST.lean.
- `EcoLib.Foundations.MissionFeasibility` (conjecture-conditional). 5 theorems; source jdhart81/viridis-canon Bridge_MissionFeasibility.lean.
- `EcoLib.Foundations.P1BitQuad`: The 8-connected bit-quad Euler formula for finite rasters: a Lean proof by vertex double counting. 7 theorems; source jdhart81/viridis-research 2026-10-28_P1.
- `EcoLib.Foundations.TCT`. 4 theorems; source jdhart81/viridis-canon series/TCT.lean.

## Held

Results the job found but did not add, with the reason. They are retried when their source changes.

- canon:P9_AI_Safety.lean: marked Exploratory in the canon (quarantined, not part of the verified spine)
- canon:series/ACCN (Run-145): does not compile at the pinned toolchain and Mathlib (2 Lean errors)
- canon:series/BCAN (Run-142): no proof file in the deposit (only statements with sorry)
- canon:series/DCAE (Run-146): does not compile at the pinned toolchain and Mathlib (2 Lean errors)
- canon:series/RCBN (Run-143): no proof file in the deposit (only statements with sorry)
- canon:series/SBRN (Run-144): no proof file in the deposit (only statements with sorry)

## Provenance

Each module's doc comment names its source repository, commit, files with SHA-256, certification and engine run. The same data is in `provenance/modules.json`; `provenance/theorems.jsonl` lists every theorem with its axioms; `provenance/held.json` lists what was held and why.

## AI use

Proofs were produced with AI assistance (Aristotle by Harmonic, OpenAI Codex, Anthropic Claude) and checked by the Lean kernel. Justin D. Hart is the accountable author; no AI tool is an author.

## License and citation

Apache-2.0 (see `LICENSE` and `NOTICE`). Cite with `CITATION.cff`.

_Updated 2026-11-08 by the viridis-engine `ecolib` workflow._
