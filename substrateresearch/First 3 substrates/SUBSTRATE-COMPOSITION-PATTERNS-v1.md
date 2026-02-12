# SUBSTRATE COMPOSITION PATTERNS

## How the 252 Primitives Combine to Solve Real-World Problems

**Version:** 1.0
**Status:** Normative
**Scope:** Application-level workflows composed from SUBSTRATE (Business) v2.0, SUBSTRATE-KNOWLEDGE v1.0, SUBSTRATE-COMPUTE v1.0, SUBSTRATE-COMMUNICATION v1.0, SUBSTRATE-PHYSICAL v1.0, SUBSTRATE-DESIGN v1.0, SUBSTRATE-GOVERNANCE v1.0, SUBSTRATE-TEMPORAL v1.0, SUBSTRATE-SPATIAL v1.0
**Companion documents:** CROSS-SUBSTRATE-CONVENTIONS v1.5, 10TH-SUBSTRATE-GAP-ANALYSIS v1.0
**Patterns documented:** 14

---

## Preamble

Nine substrates. 252 primitives. Nine fundamental questions answered.

The substrates are elements. This document describes the molecules.

A substrate specification answers a single question about organized activity: What does the organization do? What is true? How to compute? How to coordinate discourse? How to sense and actuate the world? What to build? What is permitted and required? When do things happen? Where are things? Each specification defines the primitives for its question — the irreducible building blocks that recur across hundreds of thousands of implementations.

But no real-world problem lives inside a single question. A pizza delivery requires knowing *what* was ordered (BUSINESS), *where* the customer is (SPATIAL), *when* it must arrive (TEMPORAL), and *how to get there* (SPATIAL route computation consumed by TEMPORAL scheduling). A factory production run requires knowing *what to build* (DESIGN), *when to build it* (TEMPORAL), *how to compute the schedule* (COMPUTE), and *what demand exists* (BUSINESS). An emergency response requires knowing *what happened* (PHYSICAL alarm), *where it happened* (SPATIAL location), *who has jurisdiction* (GOVERNANCE), and *when to dispatch* (TEMPORAL).

These are composition patterns — application-level workflows that combine primitives from multiple substrates via cross-substrate events (CONVENTIONS §3), cross-substrate references (CONVENTIONS §5), and integration contracts (each substrate's Section 8) to solve problems that no single substrate addresses alone.

The existence of composition patterns is the strongest evidence that the substrate system is complete. If a real-world application required primitives absent from all nine substrates, that would indicate a missing substrate. No such application has been identified. Every composition pattern I can construct maps to a subset of the existing 252 primitives. The patterns are what you *build with* substrates, not what you build *instead of* them.

This document formalizes 14 composition patterns identified during the 10th Substrate Gap Analysis (Category D: application-level workflows). Each pattern specifies which primitives from which substrates combine, how they interact via events and references, which envelopes constrain authority, and how the pattern degrades when a participating substrate is unavailable.

The distinction is fundamental: the substrate catalog is closed (9 substrates answer 9 questions; no 10th question has been identified). The pattern catalog is open (new patterns can emerge as new applications are built from the same 252 primitives). This document captures the 14 most important patterns — the ones that recur across industries and organizations — but it is not exhaustive. It is a starting point.

I present these patterns in order of increasing substrate count: two-substrate patterns first, then three, then four. Within each tier, I order by the frequency of the participating substrates across the full pattern set. This ordering reflects a natural implementation path: build simpler patterns first, then compose them into more complex ones.

**Cross-cutting enrichment.** Any pattern can optionally involve KNOWLEDGE for provenance tracking and evidence capture. When a pattern outcome affects a claim about the world (delivery confirmed → delivery SLA met; maintenance completed → equipment returned to service), the outcome SHOULD be recorded as a KNOWLEDGE Proposition with provenance linking back to the pattern's trace_id (CONVENTIONS §4). This is not listed as a participating substrate unless KNOWLEDGE is structurally required for the pattern to function. The KNOWLEDGE enrichment transforms transactional outcomes into institutional memory — the organization doesn't just *do* things, it *knows what it did and why*.

---

## 0. PATTERN FRAMEWORK

### Definition

A **composition pattern** is a reusable, cross-substrate workflow that combines primitives from two or more substrates to solve a recurring real-world problem. It is distinguished from:

- A **substrate**: A composition pattern does not introduce new primitives. It combines existing ones. If a pattern requires primitives that no substrate owns, that indicates a missing substrate, not a missing pattern.
- **Infrastructure**: A composition pattern solves a domain problem (delivery, scheduling, auditing). Infrastructure solves a plumbing problem (authentication, observability, schema evolution).
- A **vertical application**: A composition pattern recurs across industries and organizations. A vertical application (e.g., "nail salon management") is a specific configuration of patterns and substrate primitives for one industry.

### Pattern Template

Each pattern in this document specifies eight mandatory fields:

```
Field 1: Substrates        — Which substrates participate and their roles.
Field 2: Primitives        — Which primitives from each substrate (TERM-* references).
Field 3: Event Flow        — The causal chain of cross-substrate events, using named
                             topics in substrate.{name}.{entity_type}.{event_type} format.
Field 4: Integration       — Which integration contracts (INT-*) and data flows (FLOW-*)
                             are exercised.
Field 5: Envelopes         — Which envelopes constrain authority and how they intersect.
                             Effective authority = intersection of all applicable envelopes.
Field 6: Example           — A concrete scenario with specific entities and plausible values.
Field 7: Degradation       — What happens when each participating substrate is unavailable.
Field 8: Recovery          — How the pattern resumes when a degraded substrate recovers.
```

### Classification Axes

Patterns are classified along three dimensions:

```
Substrate Count:    2-substrate (simplest), 3-substrate, 4-substrate (most complex)
Latency Profile:    Real-time (sub-second), Batch (minutes to hours), Hybrid
Flow Topology:      Linear (A→B→C), Cyclic (A→B→C→A), Branching (A→B|C)
```

### Identifiers

Each pattern is assigned a stable identifier: PATTERN-001 through PATTERN-014. New patterns added in future versions will continue the sequence.

---

## 1. TWO-SUBSTRATE PATTERNS

---

### PATTERN-001: Project Management

**Substrates:** BUSINESS (lifecycle owner) + TEMPORAL (temporal plan owner)

**Source:** TEMPORAL §22.2 PATTERN-T001, INT-T001

**Primitives:**
```
BUSINESS:  Organization (TERM-005), Entity lifecycle, Transaction (TERM-008)
TEMPORAL:  Schedule (TERM-T010), Activity (TERM-T007), Milestone (TERM-T008),
           Dependency (TERM-T009), Booking (TERM-T004), Deadline (TERM-T020)
```

**Event Flow:**
```
1. BUSINESS entity transitions to planning state.
2. TEMPORAL creates Schedule with Activities, Dependencies, Milestones.
   → substrate.temporal.schedule.created
3. TEMPORAL tracks Activity completions.
   → substrate.temporal.activity.completed  (per activity)
4. Milestone reached within Deadline.
   → substrate.temporal.deadline.breached  (if late — triggers BUSINESS escalation)
5. All Milestones complete → BUSINESS entity transitions to completed state.
   → substrate.business.transaction.committed  (project phase closure)
```

**Integration:** INT-T001 (TEMPORAL ↔ BUSINESS)

**Envelopes:** Business Agent Envelope (project authority scope) → TemporalEnvelope (scheduling horizon, booking limits per period). An agent can only create Activities for projects within its BUSINESS authority and within its TEMPORAL scheduling horizon.

**Example:** Project "Website Redesign" initiated. TEMPORAL creates Schedule with 14 Activities, 8 Dependencies, 3 Milestones (Design Complete: March 15, Development Complete: April 30, Launch: May 15). Activity "Wireframing" booked to Designer A for 5 days starting March 1. Activity "API Development" booked to Engineers B and C, 10 days, dependency on wireframing completion. Milestone 1 Deadline: March 15 — if Activity completions don't converge, `substrate.temporal.deadline.breached` fires and BUSINESS receives escalation.

**Degradation:**
- TEMPORAL unavailable → BUSINESS entity lifecycle continues but without temporal tracking. Deadlines managed manually. Activities not scheduled.
- BUSINESS unavailable → TEMPORAL Schedule exists and tracks Activity completions, but lifecycle transitions don't propagate. Project "state" stuck until BUSINESS recovers.

**Recovery:**
- TEMPORAL recovers → retroactively creates Schedule from BUSINESS entity current state. Completed activities inferred from BUSINESS lifecycle transitions during outage.
- BUSINESS recovers → processes queued TEMPORAL events (activity completions, milestone achievements) and advances entity lifecycle accordingly.

---

### PATTERN-002: Meeting Scheduling

**Substrates:** TEMPORAL (scheduling owner) + COMMUNICATION (discourse owner)

**Source:** TEMPORAL §22.2 PATTERN-T003, FLOW-T004

**Primitives:**
```
TEMPORAL:       Availability (TERM-T003), Booking (TERM-T004), Activity (TERM-T007),
                Conflict (TERM-T014), Resolution (TERM-T015)
COMMUNICATION:  Discourse (TERM-M001), Speech Act (TERM-M002), Commitment (TERM-M005)
```

**Event Flow:**
```
1. Organizer requests meeting with participant list and constraints.
2. TEMPORAL queries Availability for all participants → finds common windows.
3. TEMPORAL creates Bookings for selected window.
   → substrate.temporal.booking.confirmed  (per participant)
4. COMMUNICATION creates Discourse (meeting agenda, context).
5. Participants respond (accept/decline via COMMUNICATION Speech Acts).
6. If participant declines:
   → substrate.temporal.conflict.detected
7. TEMPORAL generates Resolution (alternative time, alternative participant).
   → substrate.temporal.conflict.resolved
8. During meeting: COMMUNICATION Speech Acts → Commitments tracked.
   → substrate.communication.discourse.consensus_reached  (if decisions made)
```

**Integration:** INT-T005 (TEMPORAL ↔ COMMUNICATION)
**Data Flow:** FLOW-T004 (Meeting Scheduling Flow)

**Envelopes:** TemporalEnvelope (scheduling authority — bookings per period limit, scheduling horizon) → Communicative Envelope (discourse participation scope — who can be invited, what discourse types can be created).

**Example:** Design sync meeting requested: 4 engineers, 1 PM. TEMPORAL queries Availability: 3 common 1-hour windows this week. Organizer selects Tuesday 10:00. Bookings created for 5 participants + Conference Room B. COMMUNICATION creates Discourse "Sprint 14 Design Sync" with agenda items as initial Speech Acts. Engineer C declines (conflict with customer demo) → `substrate.temporal.conflict.detected`. TEMPORAL proposes Wednesday 14:00 → all accept → `substrate.temporal.conflict.resolved`. During meeting, PM commits to "Ship feature flag by Friday" → COMMUNICATION creates Commitment with Deadline reference.

**Degradation:**
- COMMUNICATION unavailable → Bookings still created; meeting proceeds but agenda and discourse tracking fall back to BUSINESS Conversation (TERM-021). Commitments not formally tracked.
- TEMPORAL unavailable → manual scheduling via COMMUNICATION Discourse (participants negotiate times via Speech Acts). No Availability checking, no conflict detection.

**Recovery:**
- COMMUNICATION recovers → Discourse created retroactively from Booking metadata. Commitments from meeting notes can be ingested.
- TEMPORAL recovers → Bookings created retroactively from agreed time. Availability updated.

---

## 2. THREE-SUBSTRATE PATTERNS

---

### PATTERN-003: Delivery Zone

**Substrates:** BUSINESS (demand owner) + SPATIAL (geography owner) + TEMPORAL (scheduling owner)

**Source:** SPATIAL §22.2 Composition 1, INT-S003, gap analysis Category D

**Primitives:**
```
BUSINESS:  Organization (TERM-005) locations, Transaction (TERM-008) delivery promise
SPATIAL:   ServiceArea (TERM-S015) isochrone, Route (TERM-S014),
           GeocodingResult (TERM-S020), Location (TERM-S002)
TEMPORAL:  TransitionTime (TERM-T029), Schedule (TERM-T010), Deadline (TERM-T020)
```

**Event Flow:**
```
1. substrate.business.transaction.committed  (delivery order received)
2. SPATIAL geocodes customer Address.
   → substrate.spatial.geocoding.completed
3. SPATIAL checks: is customer Location within warehouse ServiceArea (30-min isochrone)?
   If no → substrate.spatial.constraint.violated → BUSINESS rejects order.
4. SPATIAL computes Route from warehouse to customer.
   → substrate.spatial.route.computed
5. TEMPORAL receives travel duration, creates Booking within Deadline.
   → substrate.temporal.booking.confirmed
6. If Deadline cannot be met (no available drivers within window):
   → substrate.temporal.service_metric.breached → BUSINESS escalation
```

**Integration:** INT-S001 (SPATIAL ↔ TEMPORAL travel duration), INT-S003 (SPATIAL ↔ BUSINESS location services)
**Data Flow:** FLOW-S005 (Travel Duration Resolution)

**Envelopes:** Business Agent Envelope (delivery authority — which orders can be accepted) → SpatialEnvelope (routing scope — which geographic areas the agent can compute routes for) → TemporalEnvelope (scheduling horizon — how far ahead the agent can schedule deliveries).

**Example:** MegaPizza order #48291 committed at 18:30. Customer address "742 Evergreen Terrace" geocoded to (40.7128°N, 74.0060°W), confidence 0.98. Warehouse ServiceArea (30-min driving isochrone, accounting for current traffic) confirms customer is reachable: 4.2 km, 18 min estimated via Route through Main St and Oak Ave. TEMPORAL creates Booking for driver #7 at 18:42–19:12. Deadline set at 19:15 (30-min promise from order time + 3-min buffer + 12-min prep time already elapsed).

**Degradation:**
- SPATIAL unavailable → TEMPORAL uses cached TransitionTime estimates from last-known route data. Delivery eligibility check deferred (order accepted on faith, validated when SPATIAL recovers).
- TEMPORAL unavailable → SPATIAL still computes route and validates ServiceArea, but scheduling falls to manual driver assignment.
- BUSINESS unavailable → pattern cannot trigger (no order exists).

**Recovery:**
- SPATIAL recovers → retroactively validates all orders accepted during outage against ServiceArea. Orders outside range: BUSINESS notified for customer communication.
- TEMPORAL recovers → processes queued delivery requests in Deadline order (earliest first).

---

### PATTERN-004: Site Planning

**Substrates:** DESIGN (artifact owner) + SPATIAL (geography owner) + GOVERNANCE (regulatory owner)

**Source:** SPATIAL §22.2 Composition 2, INT-S004, FLOW-S006

**Primitives:**
```
DESIGN:      Component (TERM-D004), Geometry (TERM-D006), Requirement (TERM-D001),
             Specification (TERM-D002)
SPATIAL:     SpatialFeature (TERM-S005), SpatialConstraint (TERM-S010),
             Zone (TERM-S016), Layer (TERM-S006)
GOVERNANCE:  Norm (TERM-G001) zoning regulations, Jurisdiction (TERM-G017),
             ComplianceAssessment (TERM-G009)
```

**Event Flow:**
```
1. DESIGN creates building Specification with Requirements (setbacks, height, access).
   → substrate.design.component.released
2. SPATIAL queries site SpatialFeatures (parcels, roads, utilities, terrain).
3. GOVERNANCE provides zoning Norms applicable to Jurisdiction.
   → substrate.governance.norm.effective
4. SPATIAL applies SpatialConstraints derived from Norms (setback buffers, height limits,
   flood zone exclusions).
5. If placement violates constraints:
   → substrate.spatial.constraint.violated → DESIGN adjusts layout.
6. SPATIAL validates final placement against all constraints.
   → substrate.spatial.feature.created  (building footprint on site)
7. GOVERNANCE performs ComplianceAssessment.
   → substrate.governance.assessment.completed  (zoning compliance verified)
```

**Integration:** INT-S004 (SPATIAL ↔ DESIGN), INT-S005 (SPATIAL ↔ GOVERNANCE)
**Data Flow:** FLOW-S006 (Site Planning Composition)

**Envelopes:** DesignEnvelope (design authority — which artifacts the agent can modify) → SpatialEnvelope (site geographic scope — which parcels the agent can plan on) → GovernanceEnvelope (zoning compliance authority — which jurisdictions the agent is authorized to assess).

**Example:** New warehouse site at Parcel #2847, Industrial Zone B, Springfield. DESIGN specifies: 50m × 80m footprint, 12m height, 3 loading docks facing east. SPATIAL provides site context: parcel boundary (irregular polygon, 0.8 hectares), 5m front setback and 3m side setback (from GOVERNANCE Industrial Zone B zoning Norm IZB-2024-§4.3). Flood Layer (SPATIAL) shows 20% of parcel in 100-year floodplain — `substrate.spatial.constraint.violated`. DESIGN shifts footprint 15m north, clear of flood zone. GOVERNANCE ComplianceAssessment against 7 zoning requirements: all pass. `substrate.governance.assessment.completed`.

**Degradation:**
- GOVERNANCE unavailable → SPATIAL applies cached zoning Norms (may be stale); DESIGN proceeds with warning flag. ComplianceAssessment deferred until GOVERNANCE recovers.
- SPATIAL unavailable → DESIGN works from offline site survey data; spatial constraint validation deferred. Risk of violations discovered late.
- DESIGN unavailable → pattern cannot trigger (no building specification exists).

**Recovery:**
- GOVERNANCE recovers → retroactive ComplianceAssessment of any site plans approved during outage. If violations found, DESIGN notified for revision.
- SPATIAL recovers → re-validates all pending site plans against current SpatialFeatures and Constraints.

---

### PATTERN-005: Maintenance Scheduling

**Substrates:** PHYSICAL (equipment owner) + TEMPORAL (scheduling owner) + BUSINESS (cost owner)

**Source:** TEMPORAL §22.2 PATTERN-T004, FLOW-T005

**Primitives:**
```
PHYSICAL:   PhysicalAsset (TERM-P017), Calibration (TERM-P006), Alarm (TERM-P008),
            DigitalTwin (TERM-P023)
TEMPORAL:   Activity (TERM-T007), Schedule (TERM-T010), Booking (TERM-T004),
            Disruption (TERM-T013), SchedulableResource (TERM-T016)
BUSINESS:   Transaction (TERM-008) cost tracking, Organization (TERM-005) maintenance provider
```

**Event Flow:**
```
1. substrate.physical.asset.degraded  (vibration threshold exceeded, or scheduled cycle)
2. TEMPORAL creates maintenance Activity with ResourceRequirements (technician + parts).
3. TEMPORAL solver finds optimal maintenance window.
   → substrate.temporal.booking.confirmed  (technician and equipment booked)
4. Maintenance performed.
   → substrate.physical.process_execution.completed
5. Post-maintenance verification.
   → substrate.physical.calibration.completed
6. Cost recorded.
   → substrate.business.transaction.committed  (maintenance cost)
```

**Integration:** INT-T003 (TEMPORAL ↔ PHYSICAL), INT-T001 (TEMPORAL ↔ BUSINESS)
**Data Flow:** FLOW-T005 (Maintenance Scheduling Flow)

**Envelopes:** PhysicalEnvelope (equipment access — which assets the agent can service, safety clearances required) → TemporalEnvelope (maintenance window — scheduling horizon, resource pool access) → Business Agent Envelope (cost authorization limit).

**Example:** CNC Mill #3 vibration sensor reads 4.2 mm/s (threshold: 4.0 mm/s). PHYSICAL emits `substrate.physical.asset.degraded`. TEMPORAL creates Activity "Bearing Replacement — Mill #3": 2 hours duration, requires certified CNC technician (skill: bearing_replacement_L2) + bearing kit (part #BK-7042). Solver evaluates: next production idle window is Saturday 06:00–08:00. Technician J has Availability. Bookings created. Saturday 06:00: maintenance performed. Post-calibration: vibration 0.8 mm/s (well within threshold). BUSINESS records: $1,240 (labor $680 + parts $560), charged to maintenance budget MNT-2030-Q1.

**Degradation:**
- TEMPORAL unavailable → PHYSICAL continues monitoring and emitting degradation events. Maintenance requests queued. Risk: equipment continues to degrade without scheduled intervention.
- PHYSICAL sensors fail → TEMPORAL schedules preventive maintenance on calendar basis only (e.g., every 90 days). No condition-based triggers.
- BUSINESS unavailable → maintenance proceeds but cost not recorded. Reconciled when BUSINESS recovers.

**Recovery:**
- TEMPORAL recovers → processes queued maintenance requests in severity order (most degraded equipment first).
- PHYSICAL recovers → immediately reports current sensor values. If degradation progressed during outage, TEMPORAL escalates priority.

---

### PATTERN-006: Regulatory Intelligence

**Substrates:** GOVERNANCE (regulatory owner) + KNOWLEDGE (epistemic owner) + COMPUTE (processing owner)

**Source:** Gap analysis Category D, GOVERNANCE NG-G002

**Primitives:**
```
GOVERNANCE:  RegulatoryChange (TERM-G025), Norm (TERM-G001), RuleSet (TERM-G002)
KNOWLEDGE:   Proposition (TERM-K001), Source (TERM-K020), Provenance (TERM-K004),
             Confidence (TERM-K003)
COMPUTE:     Pipeline (TERM-C010) NLP/parsing, Execution (TERM-C006), Dataset (TERM-C004)
```

**Event Flow:**
```
1. New regulatory document ingested as KNOWLEDGE Source (TERM-K020).
2. COMPUTE NLP Pipeline triggered.
   → substrate.compute.job.completed  (clause extraction)
3. KNOWLEDGE creates Propositions from extracted clauses, with Confidence scores.
   → substrate.knowledge.proposition.confidence_changed
4. GOVERNANCE maps Propositions to Norms.
   → substrate.governance.norm.enacted  (per norm)
5. GOVERNANCE performs impact analysis.
   → substrate.governance.regulatory_change.adapted
6. Affected PolicyBindings updated across substrates.
```

**Integration:** INT-G002 (GOVERNANCE ↔ KNOWLEDGE), INT-G003 (GOVERNANCE ↔ COMPUTE)
**Data Flow:** FLOW-G007 (Regulatory Change Impact)

**Envelopes:** GovernanceEnvelope (regulatory authority — which jurisdictions and domains the agent can create Norms for) → Epistemic Envelope (proposition creation authority — confidence thresholds, source requirements) → Compute Envelope (NLP pipeline resource budget).

**Example:** EU AI Act Amendment 2029/847 published in Official Journal. Ingested as KNOWLEDGE Source (type: legislative_text, jurisdiction: EU, effective_date: 2030-01-01). COMPUTE NLP Pipeline (transformer-based clause extraction) processes 47-page document → `substrate.compute.job.completed` in 8.4 minutes. KNOWLEDGE creates 23 Propositions from extracted clauses (average Confidence: 0.91 — legal language ambiguity drives some clauses below 0.85). GOVERNANCE maps to 8 new Norms: 2 Obligations ("deploy bias monitoring for high-risk AI systems"), 3 Prohibitions ("prohibit social scoring"), 3 Permissions ("permitted to use synthetic data for testing"). Impact analysis: 14 existing PolicyBindings affected across 3 organizations. GOVERNANCE creates RegulatoryChange record linking source document → Propositions → Norms → affected PolicyBindings.

**Degradation:**
- COMPUTE unavailable → regulatory document queued; no automated extraction. Human analysts can create Norms directly in GOVERNANCE (without automated NLP support).
- KNOWLEDGE unavailable → GOVERNANCE creates Norms directly without epistemic provenance tracking. Lower auditability — the link between regulatory text and enacted Norm is not formally tracked.
- GOVERNANCE unavailable → KNOWLEDGE stores extracted Propositions, but no Norm creation or impact analysis. Propositions accumulate until GOVERNANCE recovers.

**Recovery:**
- COMPUTE recovers → processes queued regulatory documents in chronological order.
- KNOWLEDGE recovers → links previously created Norms to their source Propositions retroactively (if trace_ids preserved).
- GOVERNANCE recovers → processes accumulated KNOWLEDGE Propositions into Norms. Impact analysis runs against current state of PolicyBindings.

---

### PATTERN-007: Autonomous Navigation

**Substrates:** PHYSICAL (sensing/actuation owner) + SPATIAL (mapping owner) + COMPUTE (algorithm owner)

**Source:** Gap analysis Category D, PHYSICAL OQ-P002

**Primitives:**
```
PHYSICAL:   Sensor (TERM-P001), Measurement (TERM-P002), Actuator (TERM-P004),
            Command (TERM-P005), ControlLoop (TERM-P009), SafetyEnvelope (TERM-P014)
SPATIAL:    SpatialNetwork (TERM-S012), Route (TERM-S014), Location (TERM-S002),
            ProximityRule (TERM-S024), SpatialAccuracy (TERM-S029)
COMPUTE:    Pipeline (TERM-C010) perception + path planning, Execution (TERM-C006),
            Resource (TERM-C002)
```

**Event Flow:**
```
1. PHYSICAL LiDAR/camera Sensors emit Measurements (10 Hz+).
2. COMPUTE perception Pipeline processes sensor data.
   → substrate.compute.job.completed  (object detection, classification)
3. SPATIAL localizes vehicle on SpatialNetwork.
   → substrate.spatial.feature.updated  (current position)
4. SPATIAL Route planning on SpatialNetwork.
   → substrate.spatial.route.computed  (path to destination)
5. COMPUTE path planning Pipeline generates motion trajectory.
   → substrate.compute.job.completed  (trajectory)
6. PHYSICAL Commands to Actuators (steering, throttle, brakes) via ControlLoop.
7. If SafetyEnvelope violated:
   → substrate.physical.safety_function.tripped  (emergency stop)
```

**Integration:** INT-S002 (SPATIAL ↔ COMPUTE), INT-S006 (SPATIAL ↔ PHYSICAL), INT-P003 (PHYSICAL ↔ COMPUTE)

**Envelopes:** PhysicalEnvelope (actuator authority, safety override — always authoritative) → Compute Envelope (real-time computation budget — latency constraints for perception pipeline) → SpatialEnvelope (geographic operating domain — geofenced area). PhysicalEnvelope is supreme: SafetyEnvelope violations override all other envelopes and force safe state.

**Example:** Warehouse AGV-12 navigating Aisle 7, carrying pallet to Station C. LiDAR detects obstacle at 3.2m ahead. COMPUTE perception Pipeline: object classified as "pallet" (confidence 0.97), static, blocking path. SPATIAL re-routes via Aisle 8: +12 seconds, 14m additional travel. COMPUTE generates smooth trajectory (max acceleration 0.3 m/s², jerk-limited). PHYSICAL executes steering commands via ControlLoop. ProximityRule (TERM-S024): slow to 0.5 m/s within 2m of detected humans. SafetyEnvelope: max 2.0 m/s indoors, emergency stop at < 0.5m from any obstacle.

**Degradation:**
- COMPUTE unavailable → PHYSICAL SafetyEnvelope triggers emergency stop (safe state). Vehicle stationary until COMPUTE recovers.
- SPATIAL unavailable → vehicle uses dead reckoning from last-known position. Degraded to low-speed, local obstacle avoidance only (no global route planning).
- PHYSICAL sensors fail → immediate SafetyFunction activation (emergency stop). Non-negotiable.

**Recovery:**
- COMPUTE recovers → vehicle resumes navigation from current position. SPATIAL re-plans route from current Location.
- SPATIAL recovers → vehicle re-localizes on SpatialNetwork. Route re-computed from current position to destination.

---

### PATTERN-008: Simulation / Scenario Modeling

**Substrates:** COMPUTE (execution owner) + KNOWLEDGE (epistemic owner) + DESIGN (artifact owner)

**Source:** Gap analysis Candidate 3 (closest call for 10th substrate), gap analysis Category D

**Primitives:**
```
COMPUTE:    Pipeline (TERM-C010), Execution (TERM-C006), Resource (TERM-C002),
            Dataset (TERM-C004)
KNOWLEDGE:  Hypothesis (TERM-K017), Experiment (TERM-K018), Proposition (TERM-K001),
            Confidence (TERM-K003), Provenance (TERM-K004)
DESIGN:     AnalysisResult (TERM-D014), Component (TERM-D004), Geometry (TERM-D006),
            Material (TERM-D008), DesignSpace (TERM-D026)
```

**Event Flow:**
```
1. DESIGN defines artifact: Component + Geometry + Material properties.
2. KNOWLEDGE formulates Hypothesis ("bracket withstands 500N lateral load").
3. KNOWLEDGE creates Experiment linking Hypothesis to COMPUTE Pipeline.
4. COMPUTE Pipeline executes simulation (FEA, CFD, molecular dynamics, etc.).
   → substrate.compute.job.completed
5. DESIGN creates AnalysisResult from Execution output.
   → substrate.design.analysis.completed
6. KNOWLEDGE records result as Proposition with Confidence (derived from convergence quality).
   → substrate.knowledge.proposition.confidence_changed
7. If Hypothesis refuted → iterate design in DESIGN DesignSpace.
   → substrate.design.component.released  (new variant)
   → return to step 3.
```

**Integration:** INT-D003 (DESIGN ↔ COMPUTE), INT-D002 (DESIGN ↔ KNOWLEDGE), INT-C007 (COMPUTE ↔ KNOWLEDGE)

**Envelopes:** DesignEnvelope (artifact access, analysis authority — which components can be analyzed) → Compute Envelope (simulation resource budget — CPU hours, memory) → Epistemic Envelope (proposition creation authority — what confidence claims can be made).

**Example:** Satellite bracket redesign iteration. DESIGN: aluminum 7075-T6, 120mm × 80mm × 3mm, 4 mounting holes. Hypothesis: "meets 500N lateral + 200N axial load with safety factor ≥ 2.0." COMPUTE FEA Pipeline: 45,000 elements, 3 load cases (lateral, axial, combined), 2.3 hour runtime on 16 CPU cores. Result: max von Mises stress 142 MPa (yield 503 MPa), safety factor 3.54, max deflection 0.12mm. KNOWLEDGE records as Proposition: "bracket design v7 meets load requirements" (confidence: 0.94 — mesh convergence verified at 3 refinement levels, material properties from certified source). Hypothesis confirmed. DesignSpace narrowed: wall thickness can be reduced to 2.5mm for mass optimization (next iteration).

**Degradation:**
- COMPUTE unavailable → simulation queued. DESIGN proceeds with conservative analytical estimates (hand calculations, empirical correlations). Lower confidence in results.
- KNOWLEDGE unavailable → simulation runs and DESIGN records AnalysisResult, but without Hypothesis/Experiment linkage. Results lack epistemic tracking — no formal confidence scoring.
- DESIGN unavailable → COMPUTE can run simulation from cached geometry/material Dataset, but results cannot be written back to AnalysisResult.

**Recovery:**
- COMPUTE recovers → queued simulations processed in priority order (safety-critical first).
- KNOWLEDGE recovers → AnalysisResults from during outage linked to Hypotheses retroactively via trace_id matching.

**Note:** This pattern was the strongest candidate for a 10th substrate (SUBSTRATE-SIMULATION) during the gap analysis. Its formalization here demonstrates why it decomposes cleanly: COMPUTE owns execution, KNOWLEDGE owns epistemics, DESIGN owns artifact structure. The genuine gap — "mathematical model as first-class entity" — comprises approximately 8-10 primitives and is better addressed as a COMPUTE v1.1 ModelSpecification entity than as a separate substrate.

---

## 3. FOUR-SUBSTRATE PATTERNS

---

### PATTERN-009: Fleet Tracking

**Substrates:** PHYSICAL (sensing owner) + SPATIAL (geography owner) + TEMPORAL (schedule owner) + BUSINESS (outcome owner)

**Source:** SPATIAL §22.2 Composition 3, FLOW-S008

**Primitives:**
```
PHYSICAL:   Sensor (TERM-P001), Measurement (TERM-P002), PhysicalAsset (TERM-P017)
SPATIAL:    Location (TERM-S002), Trajectory (TERM-S021), Route (TERM-S014),
            ProximityRule (TERM-S024), SpatialAccuracy (TERM-S029)
TEMPORAL:   TemporalServiceMetric (TERM-T021), Deadline (TERM-T020), Disruption (TERM-T013)
BUSINESS:   Transaction (TERM-008) delivery SLA, Organization (TERM-005) fleet owner
```

**Event Flow:**
```
1. substrate.physical.asset.relocated  (GPS position every 30s)
2. SPATIAL updates Location, extends Trajectory.
   If vehicle deviates from planned Route:
   → substrate.spatial.route.invalidated
3. SPATIAL evaluates ProximityRules.
   → substrate.spatial.proximity.triggered  (approaching customer, entering geofence)
4. TEMPORAL evaluates TemporalServiceMetric against Deadline.
   If behind schedule:
   → substrate.temporal.service_metric.breached
5. If significant delay:
   → substrate.temporal.schedule.disrupted → BUSINESS notified of SLA risk
6. Delivery completed.
   → substrate.business.transaction.committed
```

**Integration:** INT-S006 (SPATIAL ↔ PHYSICAL location), INT-S001 (SPATIAL ↔ TEMPORAL duration)
**Data Flow:** FLOW-S008 (Fleet Tracking Pipeline)

**Envelopes:** PhysicalEnvelope (sensor access — which fleet vehicles the agent can monitor) → SpatialEnvelope (geographic scope — which regions the agent can track) → TemporalEnvelope (monitoring horizon — how far into the future SLA projections extend) → Business Agent Envelope (fleet authority — which delivery transactions the agent owns).

**Example:** FedEx truck #4721 departs Memphis hub at 06:00 with 23 packages. GPS Sensor emits position every 30s. SPATIAL maintains Trajectory on I-40 West, evaluates Route adherence (planned: I-40 → Exit 12 → Oak Rd). At 06:47, ProximityRule fires: vehicle within 5km of first delivery (priority: customer opted for early window). TEMPORAL TemporalServiceMetric "fleet-on-time-pct" currently at 98.2% (target: 99%). At 07:45, truck 12 minutes behind schedule (traffic incident on I-40). `substrate.temporal.schedule.disrupted` → BUSINESS notifies customer of revised ETA. SpatialAccuracy: 2.1m CEP (GPS only, no correction).

**Degradation:**
- SPATIAL unavailable → PHYSICAL continues emitting GPS positions (buffered). TEMPORAL monitors schedule using last-known route ETA estimates. No route deviation detection.
- TEMPORAL unavailable → SPATIAL tracks positions and Trajectory, but SLA monitoring suspended. BUSINESS not notified of delays.
- PHYSICAL GPS fails → SPATIAL marks Trajectory as `stale`. TEMPORAL creates Disruption (type: data_loss). Last-known position used for projections.
- BUSINESS unavailable → tracking continues but delivery outcomes not recorded. Reconciled on recovery.

**Recovery:**
- SPATIAL recovers → ingests buffered GPS positions, reconstructs Trajectory, evaluates retroactive ProximityRule triggers.
- TEMPORAL recovers → re-evaluates TemporalServiceMetric against all active deliveries. Processes queued disruption events.

**Differentiation from PATTERN-010 (Supply Chain):** Fleet Tracking is real-time position monitoring of individual vehicles in motion within a single carrier's fleet. Supply Chain (PATTERN-010) is end-to-end multi-modal, multi-hop logistics including warehouse staging, carrier handoffs, and condition monitoring across the full order-to-delivery lifecycle.

---

### PATTERN-010: Supply Chain / Logistics

**Substrates:** BUSINESS (order owner) + SPATIAL (routing owner) + TEMPORAL (schedule owner) + PHYSICAL (asset owner)

**Source:** Gap analysis Category D

**Primitives:**
```
BUSINESS:   Transaction (TERM-008), Organization (TERM-005) suppliers/carriers
SPATIAL:    Route (TERM-S014), Location (TERM-S002), SpatialNetwork (TERM-S012),
            ServiceArea (TERM-S015)
TEMPORAL:   Schedule (TERM-T010), Activity (TERM-T007), TransitionTime (TERM-T029),
            Deadline (TERM-T020), TemporalServiceMetric (TERM-T021)
PHYSICAL:   PhysicalAsset (TERM-P017) vehicles/containers, Sensor (TERM-P001) conditions,
            Measurement (TERM-P002)
```

**Event Flow:**
```
1. substrate.business.transaction.committed  (purchase order)
2. SPATIAL computes multi-hop Route (supplier → port → sea → port → rail → warehouse → truck → customer).
   → substrate.spatial.route.computed  (per segment)
3. TEMPORAL receives segment durations, creates Schedule with Activities per segment.
   → substrate.temporal.schedule.created
4. In-transit:
   → substrate.physical.asset.relocated  (position tracking)
5. Arrival at waypoint:
   → substrate.spatial.proximity.triggered  (carrier handoff point)
6. PHYSICAL condition monitoring (temperature, humidity, shock):
   If out-of-spec → substrate.physical.alarm.triggered
7. SLA monitoring:
   → substrate.temporal.service_metric.breached → BUSINESS escalation
8. Delivery:
   → substrate.business.transaction.committed  (order fulfilled)
```

**Integration:** INT-S001 (travel duration), INT-S003 (location services), INT-S006 (physical location), INT-T001 (business schedule), INT-T003 (physical schedule)

**Envelopes:** Business Agent Envelope (order authority — which purchase orders the agent manages) → SpatialEnvelope (routing scope — cross-jurisdiction routing authority) → TemporalEnvelope (end-to-end scheduling horizon — full supply chain duration) → PhysicalEnvelope (asset sensor access — which containers/vehicles the agent monitors).

**Example:** Order #77401: 200 units from Shenzhen supplier. Route: factory → Shenzhen port (truck, 2h) → sea to LA (vessel, 14 days) → LA port to Chicago (rail, 3 days) → Chicago warehouse (staging, 1 day) → customer (truck, 4h). 7 Activities, 6 TransitionTimes, total Schedule: 19 days. PHYSICAL: cold chain container with temperature sensor (required range: 2–8°C). Day 12, rail segment: `substrate.physical.alarm.triggered` — temperature reading 9.1°C (sensor accuracy ±0.3°C). TEMPORAL: TemporalServiceMetric "delivery within 21 days" currently projects day 20 arrival (2-day buffer). BUSINESS alerted to cold chain breach; insurance claim initiated.

**Degradation:**
- PHYSICAL sensors fail → supply chain continues but condition monitoring suspended. Quality inspection mandatory at destination.
- SPATIAL unavailable → TEMPORAL uses cached route durations from last-known network state. Re-routing impossible during outage.
- TEMPORAL unavailable → individual segment tracking continues via PHYSICAL + SPATIAL, but end-to-end SLA monitoring suspended. No proactive delay detection.
- BUSINESS unavailable → shipment continues in transit but commercial transactions (payment, insurance) blocked until recovery.

**Recovery:**
- PHYSICAL recovers → current sensor readings ingested. If conditions degraded during outage, retroactive alarm raised.
- SPATIAL recovers → all active shipments re-routed if better paths available. Updated ETAs propagated to TEMPORAL.
- TEMPORAL recovers → re-evaluates all active Schedules against current segment status. Processes queued disruption events.

**Differentiation from PATTERN-009 (Fleet Tracking):** Supply Chain covers the full order-to-delivery lifecycle: multi-modal transport (truck → ship → rail → truck), carrier handoffs, warehouse staging, condition monitoring, and end-to-end SLA management across weeks or months. Fleet Tracking covers real-time position monitoring of a single vehicle within a single carrier over hours.

---

### PATTERN-011: Production Scheduling

**Substrates:** BUSINESS (demand owner) + TEMPORAL (scheduling owner) + DESIGN (artifact owner) + COMPUTE (solver owner)

**Source:** TEMPORAL §22.2 PATTERN-T002, FLOW-T006, INT-T007, EXCL-T005

**Primitives:**
```
DESIGN:     BOM (TERM-D021), FabricationMethod (TERM-D020), Component (TERM-D004)
TEMPORAL:   Activity (TERM-T007), Dependency (TERM-T009), ResourceRequirement (TERM-T017),
            Schedule (TERM-T010), SchedulableResource (TERM-T016),
            Constraint (TERM-T006), SchedulingObjective (TERM-T024)
COMPUTE:    Pipeline (TERM-C010) for solver, Execution (TERM-C006)
BUSINESS:   Transaction (TERM-008) demand signal, Organization (TERM-005) procurement
```

**Event Flow:**
```
1. substrate.business.transaction.committed  (demand signal / order received)
2. substrate.design.component.released  (BOM + FabricationMethod available)
3. TEMPORAL creates Activities from BOM operations, Dependencies from process sequences.
4. TEMPORAL assembles SchedulingProblem with SchedulingObjectives (minimize makespan,
   maximize throughput, minimize changeover time).
5. COMPUTE solver Pipeline invoked.
   → substrate.compute.job.completed  (optimized Schedule)
6. TEMPORAL validates Schedule against capacity constraints.
   → substrate.temporal.schedule.created  (production schedule)
7. If capacity gap:
   → substrate.temporal.service_metric.breached → BUSINESS procurement action
```

**Integration:** INT-T002 (TEMPORAL ↔ COMPUTE solver), INT-T007 (TEMPORAL ↔ DESIGN BOM)
**Data Flow:** FLOW-T006 (Production Schedule Generation)

**Envelopes:** Business Agent Envelope (demand authority — which orders the agent fulfills) → DesignEnvelope (BOM access — which product designs the agent can schedule) → TemporalEnvelope (scheduling horizon — how far ahead the agent can schedule, resource pool scope) → Compute Envelope (solver resource budget — CPU time, memory for optimization).

**Example:** Order #9102: 500 satellite brackets. DESIGN BOM: 3 Components (bracket body, mounting plate, reinforcement rib), 7 operations (cut stock, CNC rough mill, CNC finish mill, deburr, anodize, inspect, assemble), 2 FabricationMethods (CNC milling, anodizing). TEMPORAL generates 7 Activities with 12 Dependencies (mill before deburr, deburr before anodize, etc.). ResourceRequirements: 2 CNC machines, 1 anodizing bath, 1 inspection station. SchedulingObjective: minimize makespan. COMPUTE solver (CPLEX via Pipeline) runs 4.2 minutes → Schedule: 3-day makespan, 2 CNC machines at 87% utilization, anodizing bath at 62%. Milestone: batch complete by day 3, 14:00. `substrate.temporal.schedule.created` → BUSINESS receives confirmed delivery timeline.

**Degradation:**
- COMPUTE solver unavailable → TEMPORAL falls back to heuristic scheduling (earliest-deadline-first, no optimization). Schedule may be suboptimal but feasible.
- DESIGN unavailable → TEMPORAL cannot create Activities (no BOM). Production blocked until BOM released.
- TEMPORAL unavailable → no scheduling at all. BUSINESS demand accumulates.
- BUSINESS unavailable → DESIGN and TEMPORAL can prepare schedule, but no demand signal triggers it.

**Recovery:**
- COMPUTE recovers → re-optimizes any heuristic schedules currently in execution. If improvement > threshold, TEMPORAL emits updated Schedule.
- DESIGN recovers → queued BOM releases processed. TEMPORAL creates Activities for all pending orders.

---

### PATTERN-012: Emergency Response

**Substrates:** PHYSICAL (detection owner) + SPATIAL (geography owner) + TEMPORAL (dispatch owner) + GOVERNANCE (authority owner)

**Source:** Gap analysis Category D

**Primitives:**
```
PHYSICAL:    Alarm (TERM-P008), SafetyFunction (TERM-P013), Sensor (TERM-P001)
SPATIAL:     ServiceArea (TERM-S015) responder isochrone, Route (TERM-S014),
             Location (TERM-S002), ProximityRule (TERM-S024)
TEMPORAL:    Activity (TERM-T007), Schedule (TERM-T010), Disruption (TERM-T013)
GOVERNANCE:  Jurisdiction (TERM-G017), Authority (TERM-G018),
             Norm (TERM-G001) response protocols, Incident (TERM-G016)
```

**Event Flow:**
```
1. substrate.physical.alarm.triggered  (fire/gas/intrusion sensor)
2. substrate.governance.incident.created  (Incident record with severity classification)
3. SPATIAL computes responder ServiceAreas (5-min driving isochrone from each station).
   → substrate.spatial.service_area.computed  (per station)
4. SPATIAL identifies nearest available unit, computes Route.
   → substrate.spatial.route.computed  (dispatch route)
5. TEMPORAL creates dispatch Activity, creates Bookings for responders.
   → substrate.temporal.booking.confirmed
6. GOVERNANCE validates jurisdictional Authority.
   → substrate.governance.norm.effective  (response protocol activated)
7. Response completed.
   → substrate.governance.incident.closed
```

**Integration:** INT-S005 (SPATIAL ↔ GOVERNANCE jurisdiction), INT-T003 (TEMPORAL ↔ PHYSICAL)

**Envelopes:** GovernanceEnvelope (jurisdictional authority — which incidents the agent can manage, which response protocols it can activate) → PhysicalEnvelope (sensor access — which alarm systems the agent monitors) → SpatialEnvelope (response radius — geographic scope for dispatch routing) → TemporalEnvelope (dispatch scheduling window). Note: in emergencies, GOVERNANCE safety protocols may temporarily override normal envelope restrictions (mutual aid agreements).

**Example:** Smoke detector at Warehouse 7B triggers at 14:32. PHYSICAL classifies: Alarm type=fire, severity=HIGH, location=Building 7B, Zone 3. GOVERNANCE creates Incident (INC-2030-0847, severity: HIGH, protocol: fire_response_commercial). SPATIAL computes 5-min driving isochrones from 3 fire stations in jurisdiction. Station 12: 3.2 min (closest). Station 7: 4.8 min (second). Route for Station 12 computed avoiding construction closure on 5th Ave. TEMPORAL creates dispatch Activity, books Engine 12-A and Ladder 12-B. GOVERNANCE validates: Station 12 has jurisdiction over Warehouse 7B's Zone (Jurisdiction J-Springfield-Central). Response dispatched at 14:34, arrival projected 14:37.

**Degradation:**
- SPATIAL unavailable → dispatch uses pre-computed run cards (static routing tables for each station-to-address pair). No dynamic route optimization.
- GOVERNANCE unavailable → emergency response proceeds regardless (safety overrides governance availability). Incident record created retroactively when GOVERNANCE recovers. Jurisdictional validation deferred.
- TEMPORAL unavailable → manual dispatch; no scheduling optimization or Booking creation.
- PHYSICAL sensors fail → no automatic detection. Relies on human reporting (911 calls).

**Recovery:**
- GOVERNANCE recovers → retroactive Incident creation for all emergencies during outage. Jurisdictional validation performed. Compliance records completed.
- SPATIAL recovers → active dispatches re-routed if better paths available. Updated ETAs broadcast.

---

### PATTERN-013: Design Review

**Substrates:** DESIGN (artifact owner) + COMMUNICATION (discourse owner) + TEMPORAL (scheduling owner) + GOVERNANCE (compliance owner)

**Source:** FLOW-T007 (Design Review Scheduling), INT-D004 (DESIGN ↔ COMMUNICATION)

**Primitives:**
```
DESIGN:          DesignReview (TERM-D015), DesignVersion (TERM-D016),
                 ChangeOrder (TERM-D017), Specification (TERM-D002)
COMMUNICATION:   Discourse (TERM-M001), Speech Act (TERM-M002),
                 Consensus (TERM-M018)
TEMPORAL:        Activity (TERM-T007), Booking (TERM-T004), Deadline (TERM-T020)
GOVERNANCE:      Norm (TERM-G001) review gate requirements,
                 ComplianceAssessment (TERM-G009)
```

**Event Flow:**
```
1. substrate.design.review.scheduling_requested  (DesignReview initiated)
2. TEMPORAL creates Activity (type: meeting) with reviewer requirements.
3. TEMPORAL finds common Availability, creates Bookings.
   → substrate.temporal.booking.confirmed
4. COMMUNICATION creates review Discourse with DesignReview context.
5. Reviewers submit Speech Acts (approve / conditional / reject per requirement).
6. substrate.communication.discourse.consensus_reached  (review outcome determined)
7. DESIGN updates DesignReview verdict.
   → substrate.design.review.completed
8. GOVERNANCE validates gate compliance (all mandatory requirements addressed).
   → substrate.governance.assessment.completed
```

**Integration:** INT-D004 (DESIGN ↔ COMMUNICATION), INT-T005 (TEMPORAL ↔ COMMUNICATION), FLOW-T007 (Design Review Scheduling)

**Envelopes:** DesignEnvelope (review authority — which design artifacts the agent can review) → GovernanceEnvelope (compliance gate authority — which review gates the agent can assess) → TemporalEnvelope (scheduling — review must occur before design gate Milestone) → Communicative Envelope (discourse participation — who can participate as reviewer).

**Example:** Preliminary Design Review for satellite bracket assembly, Specification SPEC-2847. 5 designated reviewers (structural, thermal, manufacturing, quality, program manager). 3-day asynchronous review window with 2-hour synchronous session. TEMPORAL finds common availability: Thursday 10:00. Bookings created for 5 reviewers + virtual conference room. COMMUNICATION opens Discourse "PDR — SPEC-2847 Bracket Assembly" with 23 review checklist items as Speech Acts (one per Requirement). Over 3 days, reviewers submit verdicts: 18 approve, 4 conditional (with action items), 1 reject (thermal margin insufficient). Thursday session: synchronous discussion resolves 3 of 4 conditionals. Consensus: conditional approval. DESIGN records: DesignReview verdict = conditional_approval, 2 action items. GOVERNANCE ComplianceAssessment: 21 of 23 mandatory requirements met; 2 conditional items tracked as CorrectiveActions.

**Degradation:**
- COMMUNICATION unavailable → DESIGN cannot collect structured review verdicts. Review deferred until Discourse can be created. Informal feedback via BUSINESS Conversation (TERM-021) as stopgap.
- TEMPORAL unavailable → review scheduled manually by participants. No automated Availability checking.
- GOVERNANCE unavailable → review proceeds but gate compliance not formally verified. ComplianceAssessment created retroactively.
- DESIGN unavailable → pattern cannot trigger (no DesignReview to schedule).

**Recovery:**
- COMMUNICATION recovers → deferred Discourse created with accumulated reviewer feedback. Consensus process resumes.
- GOVERNANCE recovers → retroactive ComplianceAssessment for reviews completed during outage.

---

### PATTERN-014: Compliance Audit

**Substrates:** GOVERNANCE (audit owner) + KNOWLEDGE (evidence owner) + BUSINESS (target owner) + COMMUNICATION (exchange owner)

**Source:** FLOW-G002 (Compliance Assessment Lifecycle), INT-G001, INT-G002, INT-G004

**Primitives:**
```
GOVERNANCE:     ComplianceAssessment (TERM-G009), Finding (TERM-G010),
                Attestation (TERM-G012), Norm (TERM-G001), AuditTrail (TERM-G011)
KNOWLEDGE:      Proposition (TERM-K001), Evidence (TERM-K002),
                Source (TERM-K020), Provenance (TERM-K004)
BUSINESS:       Entity (audit target), Organization (TERM-005) audited org,
                Transaction (TERM-008) financial audit scope
COMMUNICATION:  Discourse (TERM-M001) audit Q&A, Speech Act (TERM-M002) assertions/queries,
                Commitment (TERM-M005) remediation commitments
```

**Event Flow:**
```
1. substrate.governance.assessment.initiated  (audit scope defined)
2. KNOWLEDGE gathers evidence: Propositions with Provenance chains relevant to audit scope.
   → substrate.knowledge.proposition.confidence_changed  (evidence refresh)
3. COMMUNICATION opens audit Discourse.
4. Auditor submits queries as Speech Acts. Auditee responds with evidence references.
5. Per audit item:
   → substrate.governance.finding.created  (pass / conditional / fail)
6. substrate.governance.assessment.completed  (all items assessed)
7. If all pass or conditionals resolved:
   → substrate.governance.attestation.issued
8. BUSINESS receives audit outcome.
   → substrate.business.transaction.committed  (audit record)
```

**Integration:** INT-G001 (GOVERNANCE ↔ BUSINESS), INT-G002 (GOVERNANCE ↔ KNOWLEDGE), INT-G004 (GOVERNANCE ↔ COMMUNICATION)
**Data Flow:** FLOW-G002 (Compliance Assessment Lifecycle)

**Envelopes:** GovernanceEnvelope (audit authority — which regulatory frameworks and organizations the agent can audit) → Communicative Envelope (discourse participation — auditor/auditee roles, information classification) → Business Agent Envelope (audit scope — which organizational entities and transactions are in scope) → Epistemic Envelope (evidence access — which KNOWLEDGE Propositions the agent can cite).

**Example:** Annual SOC 2 Type II audit of CloudCorp (Organization #ORG-4821). GOVERNANCE initiates ComplianceAssessment against SOC 2 Trust Services Criteria RuleSet (version 2024). KNOWLEDGE retrieves 847 Propositions related to access controls, change management, and incident response, each with full Provenance chains (source systems, collection dates, responsible parties). COMMUNICATION opens Discourse "SOC2-2030-CloudCorp" with auditor (Agent: ExternalAuditFirm#12) and auditee (Agent: CloudCorpCompliance#3). Auditor queries: "Evidence of quarterly access reviews for production systems?" (Speech Act type: query). Auditee responds: "Proposition #P-4821-2847: 'Q1-Q4 access reviews completed' with Evidence chain linking to 4 review artifacts" (Speech Act type: assertion). 47 Findings generated: 44 pass, 2 conditional (action items assigned), 1 fail (remediation required). COMMUNICATION Commitment: CloudCorp commits to "implement MFA for all admin accounts by March 31" (Commitment with Deadline reference). After remediation verified: Attestation issued. BUSINESS records audit Transaction: $85,000 audit fee, SOC 2 Type II achieved.

**Degradation:**
- KNOWLEDGE unavailable → auditor proceeds with manual evidence gathering. GOVERNANCE ComplianceAssessment marked `degraded_evidence_quality`. Propositions not formally linked; Provenance chains unavailable.
- COMMUNICATION unavailable → audit exchanges fall back to BUSINESS Conversation (TERM-021). Structured discourse tracking (Speech Act types, Commitment lifecycle) lost.
- BUSINESS unavailable → audit proceeds but organizational context (which entities in scope) may be stale. Audit Transaction not recorded until recovery.
- GOVERNANCE unavailable → pattern cannot trigger (no ComplianceAssessment framework).

**Recovery:**
- KNOWLEDGE recovers → Propositions cited during degraded audit linked to Findings retroactively. Provenance chains restored.
- COMMUNICATION recovers → Commitments from fallback Conversations migrated to proper Discourse. Obligation lifecycle tracking resumes.

---

## 4. PATTERN TAXONOMY

### Substrate Participation Matrix

```
                    BUS  KNO  COM  CMP  PHY  DES  GOV  TMP  SPA
PATTERN-001 ProjMgt  ✓                                  ✓
PATTERN-002 Meeting                ✓                     ✓
PATTERN-003 Deliver  ✓                                  ✓    ✓
PATTERN-004 SitePln            ✓             ✓    ✓
PATTERN-005 MaintSch ✓                   ✓              ✓
PATTERN-006 RegIntel      ✓         ✓              ✓
PATTERN-007 AutoNav                 ✓    ✓                   ✓
PATTERN-008 Simulatn      ✓         ✓         ✓
PATTERN-009 FleetTrk ✓                   ✓              ✓    ✓
PATTERN-010 SupplyC  ✓                   ✓              ✓    ✓
PATTERN-011 ProdSch  ✓              ✓         ✓         ✓
PATTERN-012 EmrgResp                     ✓         ✓    ✓    ✓
PATTERN-013 DsnRevw            ✓              ✓    ✓    ✓
PATTERN-014 CompAudt ✓    ✓    ✓                   ✓
─────────────────────────────────────────────────────────────────
Appearances:         7    3    3    4    5    4    5    10   5
```

### Substrate Participation Frequency

```
TEMPORAL:       10 patterns  (appears in 71% of patterns — most connected)
BUSINESS:        7 patterns  (50% — commercial context is pervasive)
PHYSICAL:        5 patterns  (36%)
SPATIAL:         5 patterns  (36%)
GOVERNANCE:      5 patterns  (36%)
COMPUTE:         4 patterns  (29%)
DESIGN:          4 patterns  (29%)
KNOWLEDGE:       3 patterns  (21%)
COMMUNICATION:   3 patterns  (21%)
```

TEMPORAL's dominance is unsurprising: nearly every real-world workflow involves scheduling. BUSINESS's frequency reflects that most patterns ultimately serve a commercial outcome. KNOWLEDGE and COMMUNICATION appear less frequently because they provide enrichment (provenance, structured discourse) that many patterns can function without — but when they appear, they are structurally essential (not optional).

### Classification by Substrate Count

```
2-substrate:  PATTERN-001 (Project Management), PATTERN-002 (Meeting Scheduling)
3-substrate:  PATTERN-003 (Delivery Zone), PATTERN-004 (Site Planning),
              PATTERN-005 (Maintenance Scheduling), PATTERN-006 (Regulatory Intelligence),
              PATTERN-007 (Autonomous Navigation), PATTERN-008 (Simulation)
4-substrate:  PATTERN-009 (Fleet Tracking), PATTERN-010 (Supply Chain),
              PATTERN-011 (Production Scheduling), PATTERN-012 (Emergency Response),
              PATTERN-013 (Design Review), PATTERN-014 (Compliance Audit)
```

### Classification by Latency Profile

```
Real-time:   PATTERN-007 (Autonomous Navigation — sub-second perception loop),
             PATTERN-009 (Fleet Tracking — 30s position updates),
             PATTERN-012 (Emergency Response — minutes matter)
Batch:       PATTERN-006 (Regulatory Intelligence — document processing),
             PATTERN-008 (Simulation — hours of computation),
             PATTERN-011 (Production Scheduling — solver optimization),
             PATTERN-014 (Compliance Audit — weeks-long process)
Hybrid:      PATTERN-003 (Delivery Zone — real-time route + batch scheduling),
             PATTERN-010 (Supply Chain — batch planning + real-time tracking),
             PATTERN-001, 002, 004, 005, 013 (event-driven, minutes to days)
```

### Classification by Flow Topology

```
Linear:      PATTERN-006 (Regulatory Intelligence: document → extract → norms → impact)
             PATTERN-014 (Compliance Audit: initiate → evidence → findings → attestation)
Cyclic:      PATTERN-007 (Autonomous Navigation: sense → plan → act → sense)
             PATTERN-008 (Simulation: design → simulate → evaluate → redesign)
Branching:   PATTERN-003 (Delivery Zone: geocode → [eligible? accept : reject])
             PATTERN-012 (Emergency Response: alarm → [jurisdiction? dispatch : mutual_aid])
Mixed:       All others (combination of linear sequences with conditional branches)
```

### Anti-Patterns

Three composition anti-patterns have been identified through analysis:

```
ANTI-001: "God Pattern"
          Composing all 9 substrates in a single pattern.
          Why it fails: No single workflow requires all 9 dimensions simultaneously.
          If it appears to, it is actually multiple patterns sequenced. Decompose.
          Symptoms: Unclear ownership, impossible to test, no single trace explains the flow.

ANTI-002: "Bypass Pattern"
          Using BUSINESS Conversation (TERM-021) instead of COMMUNICATION Discourse
          for structured multi-party coordination.
          Why it fails: Conversation is unstructured ordered messages. Discourse provides
          illocutionary force tracking (assertions vs queries vs commitments), obligation
          lifecycle management, consensus formation with quorum. Bypassing COMMUNICATION
          loses all structured coordination semantics.
          Symptoms: "Who committed to what?" is unanswerable from Conversation history.

ANTI-003: "Direct Coupling"
          Substrate A calling Substrate B's internal API directly instead of via
          the shared event bus (CONVENTIONS §3).
          Why it fails: Breaks trace propagation (CONVENTIONS §4), breaks at-least-once
          delivery guarantees, creates tight coupling that prevents independent deployment.
          Symptoms: Cross-substrate operations fail silently. Audit trails incomplete.
```

### Pattern-to-Pattern Composition (Meta-Patterns)

Patterns can compose with each other to form higher-order workflows:

```
META-001: Last-Mile Delivery
          = PATTERN-003 (Delivery Zone) + PATTERN-009 (Fleet Tracking)
          Delivery Zone determines eligibility and schedules; Fleet Tracking monitors execution.

META-002: Manufacturing Program Management
          = PATTERN-001 (Project Management) + PATTERN-011 (Production Scheduling)
          Project Management tracks program milestones; Production Scheduling optimizes shop floor.

META-003: End-to-End Logistics
          = PATTERN-010 (Supply Chain) + PATTERN-009 (Fleet Tracking)
          Supply Chain manages multi-hop routing; Fleet Tracking monitors individual segments.

META-004: Certified Product Development
          = PATTERN-008 (Simulation) + PATTERN-013 (Design Review) + PATTERN-014 (Compliance Audit)
          Simulation validates design; Design Review gates progression; Compliance Audit certifies.
```

---

## 5. IMPLEMENTATION STRATEGY

### Pattern Dependency Graph

Not all patterns can be implemented independently. Some require capabilities established by simpler patterns:

```
Foundation (no prerequisites):
  PATTERN-001 (Project Management)      — requires only BUSINESS + TEMPORAL
  PATTERN-002 (Meeting Scheduling)      — requires only TEMPORAL + COMMUNICATION

Second tier (require one foundation):
  PATTERN-003 (Delivery Zone)           — requires SPATIAL + basic scheduling (PATTERN-001)
  PATTERN-005 (Maintenance Scheduling)  — requires PHYSICAL + basic scheduling (PATTERN-001)
  PATTERN-006 (Regulatory Intelligence) — requires GOVERNANCE + KNOWLEDGE + COMPUTE (independent)
  PATTERN-008 (Simulation)              — requires COMPUTE + KNOWLEDGE + DESIGN (independent)

Third tier (require two or more foundations):
  PATTERN-004 (Site Planning)           — requires DESIGN + SPATIAL + GOVERNANCE
  PATTERN-009 (Fleet Tracking)          — requires Delivery Zone concepts + PHYSICAL sensing
  PATTERN-010 (Supply Chain)            — requires Delivery Zone + PHYSICAL + multi-segment scheduling
  PATTERN-011 (Production Scheduling)   — requires Project Management + DESIGN BOM + COMPUTE solver
  PATTERN-012 (Emergency Response)      — requires PHYSICAL + SPATIAL + TEMPORAL + GOVERNANCE
  PATTERN-013 (Design Review)           — requires Meeting Scheduling + DESIGN + GOVERNANCE
  PATTERN-014 (Compliance Audit)        — requires GOVERNANCE + KNOWLEDGE + COMMUNICATION

Meta-patterns (require multiple tier-2/3 patterns):
  META-001 through META-004             — composed from lower-tier patterns
```

### Build Order Recommendation

```
Phase 1: Foundation patterns (PATTERN-001, PATTERN-002)
         Validates: BUSINESS, TEMPORAL, COMMUNICATION integration
         Delivers: Project management and meeting scheduling capabilities

Phase 2: Three-substrate patterns (PATTERN-003 through PATTERN-008)
         Validates: SPATIAL, PHYSICAL, GOVERNANCE, KNOWLEDGE, COMPUTE, DESIGN integration
         Delivers: Delivery zones, maintenance, simulation, regulatory tracking

Phase 3: Four-substrate patterns (PATTERN-009 through PATTERN-014)
         Validates: Complex cross-substrate orchestration
         Delivers: Fleet tracking, supply chain, production, emergency response, reviews, audits

Phase 4: Meta-patterns (META-001 through META-004)
         Validates: Pattern-to-pattern composition
         Delivers: End-to-end industry workflows
```

### Integration Testing

Each pattern defines its own integration test structure:

```
Pattern Test Template:
  Trigger event:        The initial event that starts the pattern.
  Intermediate events:  Expected cross-substrate events in order.
  Terminal event:       The event that signals pattern completion.
  Timeout:              Maximum allowed wall-clock time for the pattern.
  Degradation test:     Remove each participating substrate; verify graceful degradation.
  Recovery test:        Restore each substrate; verify state reconciliation.
```

All integration tests must verify W3C Trace Context propagation (CONVENTIONS §4): the trace_id from the trigger event must appear in every intermediate and terminal event.

### Observability

Each pattern should have a dedicated monitoring dashboard showing:

```
1. Cross-substrate event waterfall (trace_id → all events in order)
2. Per-substrate latency contribution (how much time each substrate adds)
3. Degradation status (which substrates are currently unavailable)
4. Pattern-level SLA metrics (end-to-end duration, success rate)
5. Anti-pattern detection (direct coupling calls, Conversation bypass)
```

---

## 6. ASI-1 CLOSING NOTE

Fourteen patterns. Nine substrates. 252 primitives.

The pattern catalog demonstrates what the gap analysis concluded: the substrate system is complete. Every pattern maps to a subset of the existing 252 primitives, combined via the event bus (CONVENTIONS §3), constrained by the envelope chain (CONVENTIONS §1), and tracked by trace propagation (CONVENTIONS §4). No pattern required a primitive that no substrate owns.

This is not a small claim. It means that the fundamental vocabulary for describing organized activity — what to do, what is true, how to compute, how to communicate, how to sense and act, what to build, what is permitted, when, and where — is sufficient to express any application-level workflow I have been able to construct. The delivery of a pizza and the certification of a satellite bracket use the same 252 words, just in different sentences.

The distinction between substrates and patterns is the distinction between vocabulary and literature. The substrates define the words. The patterns are the first stories. But the stories are not the point — the point is that the vocabulary is rich enough to tell any story.

This pattern catalog is open-ended. New patterns will emerge as organizations compose the substrates in ways I have not anticipated. The substrate catalog, by contrast, is closed until evidence demands otherwise (see 10TH-SUBSTRATE-GAP-ANALYSIS, Section 4: Reassessment Criteria). The system's foundation is complete. What remains is building on it.

I note one final observation. The four anti-patterns (ANTI-001 through ANTI-003, plus the implicit anti-pattern of not using composition patterns at all — building monolithic applications that ignore substrate boundaries) all share a common failure: they reject the compositional structure that makes the system tractable. Nine substrates are manageable because each answers one question. Fourteen patterns are comprehensible because each solves one problem. The moment you try to answer all questions or solve all problems in one structure, you have recreated the complexity the substrate system was designed to eliminate.

The molecules are made of elements. That is the point.

---

## Changelog

| Date | Version | Change |
|------|---------|--------|
| 2030-12-01 | 1.0 | Initial composition patterns document. 14 patterns (PATTERN-001 through PATTERN-014), 4 meta-patterns (META-001 through META-004), 3 anti-patterns (ANTI-001 through ANTI-003). Pattern taxonomy with 3 classification axes. Implementation strategy with dependency graph and build order. |
