# CROSS-SUBSTRATE CONVENTIONS

**Version:** 2.0
**Status:** Normative
**Applies to:** SUBSTRATE (Business) v2.1, SUBSTRATE-KNOWLEDGE v1.1, SUBSTRATE-COMPUTE v1.1, SUBSTRATE-COMMUNICATION v1.1, SUBSTRATE-PHYSICAL v1.1, SUBSTRATE-DESIGN v1.1, SUBSTRATE-GOVERNANCE v1.1, SUBSTRATE-TEMPORAL v1.1, SUBSTRATE-SPATIAL v1.0

---

## Purpose

This document defines shared conventions that all substrate specifications must follow. It is the authoritative source for cross-substrate interoperability patterns. Individual substrate specifications reference this document rather than redefining shared infrastructure.

---

## 1. Shared Identity

All substrates use a single Identity Provider. SUBSTRATE (Business) DEP-002 (Identity Provider / SSO) is the authoritative identity source.

**Rules:**
- One authentication = access to all substrates within permission scope.
- Agent identity is assigned in SUBSTRATE (Business) via Agent Envelope (TERM-030). Domain-specific envelopes in GOVERNANCE (TERM-G026), KNOWLEDGE (TERM-K022), TEMPORAL (TERM-T025), SPATIAL (TERM-S027), DESIGN (TERM-D024), COMPUTE (TERM-C019), COMMUNICATION (TERM-M013), and PHYSICAL (TERM-P015) extend — but never exceed — the base authority. PHYSICAL's PhysicalEnvelope is the most restrictive in the chain by design (ASM-P007). GOVERNANCE's GovernanceEnvelope sits between Business and Epistemic because normative constraints must be established before any domain-specific authority (ASM-G005). TEMPORAL's TemporalEnvelope sits between Epistemic and Spatial because temporal authority (scheduling horizon, resource pool access, conflict resolution) is a resource-allocation step that must be established after reasoning permission but before geographic scope commitment (ASM-T005). SPATIAL's SpatialEnvelope sits between Temporal and Design because spatial authority (geographic scope, routing authority, zone management) must be established after temporal scope but before design authority — an agent needs to know where it can act before deciding what to build there (ASM-S005). DESIGN's DesignEnvelope sits between Spatial and Compute because design authority is needed before compute resources or physical access (ASM-D005).
- **Envelope chain (least to most restrictive):** Business Agent Envelope → GovernanceEnvelope → Epistemic Envelope → TemporalEnvelope → SpatialEnvelope → DesignEnvelope → Compute Envelope → Communicative Envelope → PhysicalEnvelope. Effective authority = intersection of all applicable envelopes.
- Identity tokens carry: `agent_id`, `organization_id`, `principal_id`, `substrate_scopes[]`.
- All substrates validate tokens against the same Identity Provider. No substrate maintains a separate user/agent registry.
- If a domain-specific envelope does not exist for an agent in a given substrate, the agent has zero authority in that domain (deny by default).

---

## 2. Shared Organization

Organization (SUBSTRATE Business TERM-005) is the universal scoping unit across all substrates.

**Rules:**
- All entities in all substrates belong to exactly one Organization.
- SUBSTRATE (Business) is the authoritative source for Organization CRUD (create, read, update, delete).
- Other substrates receive Organization configuration via cross-substrate events on topic `substrate.business.organization.*`.
- Organization creation in Business triggers provisioning events consumed by all other substrates to initialize their org-scoped resources.
- Organization deletion/suspension in Business triggers cascading suspension events. Each substrate handles suspension according to its own safety requirements (e.g., COMPUTE drains running jobs; KNOWLEDGE marks all propositions as org-suspended; COMMUNICATION closes active discourses).

---

## 3. Shared Event Bus

All substrates emit domain events to a shared event bus. This enables cross-substrate workflows without tight coupling.

### Topic Naming Convention

```
substrate.{substrate_name}.{entity_type}.{event_type}
```

**Examples:**
- `substrate.knowledge.proposition.confidence_changed`
- `substrate.compute.job.completed`
- `substrate.communication.discourse.consensus_reached`
- `substrate.business.transaction.committed`
- `substrate.physical.safety_function.tripped`
- `substrate.physical.asset.locked_out`
- `substrate.physical.process_execution.completed`
- `substrate.physical.alarm.escalation_required`
- `substrate.physical.calibration.completed`
- `substrate.design.component.released`
- `substrate.design.change_order.completed`
- `substrate.design.analysis.completed`
- `substrate.design.review.completed`
- `substrate.design.configuration.validated`
- `substrate.design.material.property_discrepancy`
- `substrate.governance.norm.enacted`
- `substrate.governance.norm.effective`
- `substrate.governance.violation.confirmed`
- `substrate.governance.assessment.completed`
- `substrate.governance.incident.closed`
- `substrate.governance.consent.revoked`
- `substrate.governance.regulatory_change.adapted`
- `substrate.temporal.booking.confirmed`
- `substrate.temporal.booking.cancelled`
- `substrate.temporal.schedule.created`
- `substrate.temporal.schedule.disrupted`
- `substrate.temporal.conflict.detected`
- `substrate.temporal.conflict.resolved`
- `substrate.temporal.disruption.recovered`
- `substrate.temporal.service_metric.breached`
- `substrate.temporal.deadline.breached`
- `substrate.temporal.scheduling_policy.violated`
- `substrate.temporal.activity.completed`
- `substrate.spatial.feature.created`
- `substrate.spatial.feature.updated`
- `substrate.spatial.route.computed`
- `substrate.spatial.route.invalidated`
- `substrate.spatial.zone.created`
- `substrate.spatial.zone.boundary_modified`
- `substrate.spatial.territory.assigned`
- `substrate.spatial.territory.rebalanced`
- `substrate.spatial.proximity.triggered`
- `substrate.spatial.change.detected`
- `substrate.spatial.constraint.violated`
- `substrate.spatial.geocoding.completed`
- `substrate.spatial.geocoding.ambiguous`
- `substrate.spatial.service_area.computed`
- `substrate.spatial.coverage.computed`
- `substrate.spatial.envelope.violation`
- `substrate.governance.federation.proposed`
- `substrate.governance.federation.activated`
- `substrate.governance.federation.suspended`
- `substrate.governance.federation.revoked`
- `substrate.governance.federation.bridge_suspended`
- `substrate.governance.consent.gate_blocked`

### Event Schema

Every cross-substrate event carries the following envelope:

```
{
  event_id:        UUID,          // globally unique
  timestamp:       ISO-8601,      // when the event occurred
  substrate:       string,        // "business" | "knowledge" | "compute" | "communication" | "physical" | "design" | "governance" | "temporal" | "spatial"
  organization_id: UUID,          // scoping — events are always org-scoped
  entity_type:     string,        // the type of entity that changed
  entity_id:       UUID,          // the specific entity
  event_type:      string,        // what happened (created, updated, deleted, etc.)
  payload:         object,        // substrate-specific event data
  trace_id:        string,        // W3C traceparent — see Section 4
  caused_by:       UUID?          // optional — event_id of the upstream event that triggered this one
}
```

### Delivery Guarantees
- **At-least-once delivery.** Consumers must be idempotent.
- **Ordering:** Events from the same entity are delivered in order. No cross-entity ordering guarantee.
- **Schema registry:** All event payloads are registered in a shared schema registry. Breaking changes require a new event_type, not a modified schema.
- **Retention:** Events are retained for a minimum of 90 days. Substrates that need longer retention (e.g., KNOWLEDGE for provenance, PHYSICAL for regulated industries — minimum 7 years, DESIGN for buildings/infrastructure — minimum 100 years, GOVERNANCE for regulatory compliance — minimum 7 years financial, 30 years safety, indefinite for some jurisdictions, TEMPORAL for compliance-relevant schedules — minimum 7 years matching GOVERNANCE, SPATIAL for cadastral/land records — minimum 100 years, fleet positions — minimum 90 days) maintain their own event stores.

---

## 4. Cross-Substrate Trace Propagation

All cross-substrate operations propagate trace context using the W3C Trace Context standard (`traceparent` header).

**Rules:**
- When Substrate A triggers an operation in Substrate B, the `trace_id` propagates.
- Each substrate creates its own spans within the shared trace.
- The `caused_by` field in the event schema links events across substrates within the same trace.
- Enables end-to-end auditing: e.g., "Business workflow triggered Compute pipeline which produced Knowledge evidence which was debated in Communication discourse."

**Trace ID Format:** W3C `traceparent` — `{version}-{trace_id}-{parent_id}-{trace_flags}`

---

## 5. Cross-Substrate Reference Format

When any entity in one substrate needs to reference an entity in another substrate, it uses the following canonical format:

```
{
  substrate:   "business" | "knowledge" | "compute" | "communication" | "physical" | "design" | "governance" | "temporal" | "spatial",
  entity_type: string,      // e.g., "proposition", "job", "discourse", "transaction"
  entity_id:   UUID,
  version:     integer?     // optional — for referencing a specific version of a versioned entity
}
```

**Resolution Rules:**
- References are resolved by the owning substrate. The referencing substrate does not cache or replicate the referenced entity.
- If the owning substrate is unavailable, the reference is marked as `unresolvable` and queued for resolution when the substrate recovers.
- Stale references (entity deleted in owning substrate) are handled by each substrate's error model. The general pattern: mark the reference as `dangling`, log a warning, and continue operating without the referenced data.
- References are immutable once created. If the referenced entity changes, the version field (when present) ensures the reference still points to the expected state.

---

## 6. Master Boundary Principles

These four principles govern all boundary decisions between substrates. When a concept appears to belong in multiple substrates, apply these principles in order to determine ownership.

**P1 — Content vs Process.** KNOWLEDGE owns the *content* of reasoning (propositions, evidence, confidence, logical structure). COMMUNICATION owns the *process* of reasoning exchange (speech acts, discourse, turn-taking, consensus-building).

**P2 — Trigger vs Deliver.** Other substrates define *when* and *why* a message should be sent. COMMUNICATION defines *how* it is delivered, tracked, and responded to.

**P3 — Define vs Enforce.** BUSINESS *defines* organizational resources (budgets, roles, permissions). Domain substrates (KNOWLEDGE, COMPUTE, COMMUNICATION, PHYSICAL, DESIGN, GOVERNANCE, TEMPORAL, SPATIAL) *enforce* those limits within their domains and *report back* results. PHYSICAL additionally enforces PhysicalConstraints (immutable equipment limitations) that no software — including BUSINESS — can override. DESIGN additionally enforces DesignEnvelope bounds on AI design authority, with release approval non-delegable to AI for safety-critical artifacts. GOVERNANCE additionally enforces GovernanceEnvelope bounds on AI governance authority, with adjudication, sanctioning, risk acceptance, attestation issuance, and norm enactment categorically non-delegable to AI. TEMPORAL additionally enforces TemporalEnvelope bounds on AI scheduling authority (horizon, bookings/period, resource pool access, conflict resolution authority, constraint relaxation authority), and proactively enforces GOVERNANCE Norms with temporal_constraint_spec as SchedulingPolicy compliance constraints during schedule creation. SPATIAL additionally enforces SpatialEnvelope bounds on AI spatial authority (max geographic scope, geocoding/routing/zone modification authority, feature creation authority, territory assignment authority, spatial accuracy thresholds), and applies GOVERNANCE zoning/land-use Norms as SpatialConstraints during zone and feature operations.

**P4 — One Owner, Many References.** Each primitive has exactly one owning substrate. Other substrates may reference it via cross-substrate Reference (Section 5) but do not redefine it.

---

## 7. Primitive Ownership Table

| Primitive | Owner | Referenced By | Principle |
|-----------|-------|---------------|-----------|
| Organization | Business (TERM-005) | All substrates | P4 |
| Identity / Agent | Business (TERM-030) | All substrates | P4 |
| Transaction (financial) | Business (TERM-008) | Compute (cost reporting) | P3 |
| Conversation (basic messaging) | Business (TERM-021) | Communication (bridge) | P2 |
| Notification (trigger) | Business (TERM-020) | Communication (delivery) | P2 |
| Proposition (claim content) | Knowledge (TERM-K001) | Communication (assertion content) | P1 |
| Argument (reasoning chain) | Knowledge (TERM-K015) | Communication (discourse argument) | P1 |
| Consensus (epistemic record) | Knowledge (TERM-K023) | Communication (formation process) | P1 |
| Contradiction (logical state) | Knowledge (TERM-K009) | Communication (disagreement reveals it) | P1 |
| Provenance (epistemic) | Knowledge (TERM-K004) | Compute (computational provenance) | P4 |
| Budget (operational limits) | Compute (ENT-C018) | Business (financial allocation) | P3 |
| Pipeline (computational DAG) | Compute (TERM-C010) | Business (workflow may trigger) | P4 |
| Discourse (structured exchange) | Communication (TERM-M001) | Business (promoted conversation) | P2 |
| Speech Act (illocutionary act) | Communication (TERM-M002) | — | P4 |
| Consensus (formation process) | Communication (TERM-M018) | Knowledge (discourse_consensus_ref) | P1 |
| Agent Envelope (business) | Business (TERM-030) | All substrates (base authority) | P3 |
| Epistemic Envelope | Knowledge (TERM-K022) | — | P3 |
| Compute Envelope | Compute (TERM-C019) | — | P3 |
| Communicative Envelope | Communication (TERM-M013) | — | P3 |
| Sensor (physical measurement source) | Physical (TERM-P001) | Knowledge (as Source TERM-K020) | P4 |
| Measurement (timestamped reading) | Physical (TERM-P002) | Knowledge (as Observation TERM-K019) | P1 |
| Actuator (physical effect mechanism) | Physical (TERM-P004) | — | P4 |
| Command (authorized instruction) | Physical (TERM-P005) | — | P4 |
| Calibration (instrument accuracy) | Physical (TERM-P006) | Knowledge (source reliability TERM-K021) | P4 |
| SafetyFunction (safe state mechanism) | Physical (TERM-P013) | — | P4 |
| SafetyEnvelope (operating constraints) | Physical (TERM-P014) | — | P3 |
| PhysicalEnvelope (AI physical authority) | Physical (TERM-P015) | Business (chained from TERM-030) | P3 |
| PhysicalAsset (equipment) | Physical (TERM-P017) | Business (financial tracking) | P4 |
| Process (transformation spec) | Physical (TERM-P019) | — | P4 |
| Alarm (condition demanding attention) | Physical (TERM-P008) | Business (notification trigger), Communication (escalation discourse) | P2 |
| ControlLoop (feedback mechanism) | Physical (TERM-P009) | Compute (MPC optimization) | P1 |
| HazardAnalysis (risk assessment) | Physical (TERM-P016) | Knowledge (as Proposition with evidence) | P1 |
| DigitalTwin (virtual representation) | Physical (TERM-P023) | Compute (simulation Pipeline), Knowledge (prediction accuracy) | P1 |
| Requirement (testable statement) | Design (TERM-D001) | — | P4 |
| Specification (versioned requirements collection) | Design (TERM-D002) | Business (document tracking), Physical (SafetyEnvelope source) | P3 |
| DesignRationale (decision record) | Design (TERM-D003) | Knowledge (argument/evidence links) | P1 |
| Component (design unit) | Design (TERM-D004) | Physical (as PhysicalAsset TERM-P017), Business (entity tracking) | P4 |
| Assembly (composed structure) | Design (TERM-D005) | — | P4 |
| Geometry (physical shape) | Design (TERM-D006) | Compute (simulation input) | P4 |
| Topology (abstract connectivity) | Design (TERM-D007) | — | P4 |
| Material (characterized substance) | Design (TERM-D008) | Knowledge (property truth as Proposition) | P1 |
| MaterialProperty (measurable characteristic) | Design (TERM-D009) | Knowledge (Proposition with confidence) | P1 |
| Constraint (design space limitation) | Design (TERM-D010) | Knowledge (scientific basis as Proposition) | P1 |
| Tolerance (permissible variation) | Design (TERM-D011) | Physical (Measurement verification TERM-P002) | P1 |
| Standard (external normative document) | Design (TERM-D012) | Knowledge (as Source TERM-K020) | P4 |
| TestCriterion (requirement verification) | Design (TERM-D013) | — | P4 |
| AnalysisResult (simulation output) | Design (TERM-D014) | Compute (Execution TERM-C004), Knowledge (as Observation) | P1 |
| DesignReview (maturity gate evaluation) | Design (TERM-D015) | Communication (review Discourse TERM-M001) | P2 |
| DesignVersion (immutable snapshot) | Design (TERM-D016) | — | P4 |
| ChangeOrder (released design modification) | Design (TERM-D017) | Communication (approval Discourse), Business (workflow) | P2 |
| Configuration (valid version combination) | Design (TERM-D018) | — | P4 |
| Variant (declared variation point) | Design (TERM-D019) | — | P4 |
| FabricationMethod (manufacturing spec) | Design (TERM-D020) | Physical (Process TERM-P019) | P4 |
| BillOfMaterials (production parts list) | Design (TERM-D021) | Business (Transaction cost tracking) | P3 |
| Drawing (2D production representation) | Design (TERM-D022) | — | P4 |
| Interface (component boundary) | Design (TERM-D023) | Communication (negotiation Discourse) | P2 |
| DesignEnvelope (AI design authority) | Design (TERM-D024) | Business (chained from TERM-030), Knowledge (chained from TERM-K022) | P3 |
| ParametricRelation (parameter math) | Design (TERM-D025) | — | P4 |
| DesignSpace (exploration region) | Design (TERM-D026) | Compute (Pipeline TERM-C010), Knowledge (Hypothesis/Experiment) | P1 |
| Annotation (design commentary) | Design (TERM-D028) | Communication (promoted to Speech Act TERM-M002) | P2 |
| Norm (atomic normative statement) | Governance (TERM-G001) | Knowledge (as Proposition TERM-K001) | P1 |
| RuleSet (versioned norm collection) | Governance (TERM-G002) | — | P4 |
| Interpretation (norm applicability determination) | Governance (TERM-G003) | Knowledge (Argument TERM-K015) | P1 |
| PolicyBinding (norm-to-entity linkage) | Governance (TERM-G004) | All substrates (enforcement targets) | P3 |
| Obligation (normative requirement) | Governance (TERM-G005) | Communication (discourse-originated TERM-M016) | P1 |
| Permission (normative authority grant) | Governance (TERM-G006) | Business (mechanism TERM-007) | P3 |
| Prohibition (explicit action bar) | Governance (TERM-G007) | — | P4 |
| Delegation (governance authority transfer) | Governance (TERM-G008) | Communication (communicative act TERM-M020) | P1 |
| ComplianceAssessment (conformity evaluation) | Governance (TERM-G009) | — | P4 |
| Finding (assessment determination) | Governance (TERM-G010) | — | P4 |
| AuditTrail (tamper-evident record) | Governance (TERM-G011) | All substrates (cross-substrate evidence) | P4 |
| Attestation (formal compliance declaration) | Governance (TERM-G012) | — | P4 |
| Risk (adverse event possibility) | Governance (TERM-G013) | Physical (HazardAnalysis TERM-P016), Knowledge (Confidence TERM-K003) | P1 |
| Control (risk mitigation measure) | Governance (TERM-G014) | — | P4 |
| RiskAssessment (structured risk evaluation) | Governance (TERM-G015) | Physical (HazardAnalysis link) | P1 |
| Incident (adverse event record) | Governance (TERM-G016) | Business (notification trigger), Communication (escalation) | P2 |
| Jurisdiction (normative authority scope) | Governance (TERM-G017) | Compute (computation jurisdiction) | P3 |
| Authority (norm-empowered entity) | Governance (TERM-G018) | Business (SovereignAuthority ACT-007) | P3 |
| JurisdictionMapping (multi-jurisdiction resolution) | Governance (TERM-G019) | — | P4 |
| Violation (detected norm breach) | Governance (TERM-G020) | — | P4 |
| Sanction (enforcement consequence) | Governance (TERM-G021) | — | P4 |
| CorrectiveAction (remediation step) | Governance (TERM-G022) | — | P4 |
| Appeal (governance challenge) | Governance (TERM-G023) | Communication (hearing Discourse TERM-M001) | P2 |
| Exemption (obligation release) | Governance (TERM-G024) | — | P4 |
| RegulatoryChange (external requirement change) | Governance (TERM-G025) | Design (Standard TERM-D012 lifecycle) | P4 |
| GovernanceEnvelope (AI governance authority) | Governance (TERM-G026) | Business (chained from TERM-030), Knowledge (chained to TERM-K022) | P3 |
| ConsentRecord (informed agreement) | Governance (TERM-G027) | Communication (Commitment TERM-M005) | P2 |
| Calendar (temporal container) | Temporal (TERM-T001) | Business (working periods), Physical (maintenance windows) | P4 |
| TimeWindow (bounded interval) | Temporal (TERM-T002) | — | P4 |
| Availability (computed schedulable periods) | Temporal (TERM-T003) | Physical (equipment state → availability mapping) | P4 |
| Booking (temporal allocation) | Temporal (TERM-T004) | Business (Reservation TERM-023 references for commercial terms) | P4 |
| Recurrence (repeating pattern engine) | Temporal (TERM-T005) | Business (Schedule TERM-017 recurring type delegates RFC 5545 RRULE), Compute (Schedule TERM-C007 recurring type) | P4 |
| Constraint (temporal relationship) | Temporal (TERM-T006) | Governance (Norm temporal_constraint_spec consumed as SchedulingPolicy) | P3 |
| Activity (schedulable work unit) | Temporal (TERM-T007) | Design (DesignReview scheduling), Physical (maintenance scheduling) | P4 |
| Milestone (zero-duration schedule marker) | Temporal (TERM-T008) | — | P4 |
| Dependency (activity sequencing link) | Temporal (TERM-T009) | Design (BOM process sequences) | P4 |
| Schedule (constraint-satisfaction result) | Temporal (TERM-T010) | Business (project temporal plan), Compute (solver invocation) | P4 |
| Timeline (immutable schedule snapshot) | Temporal (TERM-T011) | — | P4 |
| Horizon (schedule temporal boundary) | Temporal (TERM-T012) | — | P4 |
| Disruption (schedule-invalidating event) | Temporal (TERM-T013) | Physical (asset.degraded → Disruption), Communication (participant decline → Disruption) | P2 |
| Conflict (detected scheduling collision) | Temporal (TERM-T014) | — | P4 |
| Resolution (conflict decision record) | Temporal (TERM-T015) | — | P4 |
| SchedulableResource (entity with calendar) | Temporal (TERM-T016) | Physical (PhysicalAsset TERM-P017 state maps to availability), Business (workforce) | P4 |
| ResourceRequirement (declarative resource need) | Temporal (TERM-T017) | — | P4 |
| Shift (recurring working time pattern) | Temporal (TERM-T018) | — | P4 |
| Rotation (cyclical assignment distribution) | Temporal (TERM-T019) | — | P4 |
| Deadline (temporal bound with escalation) | Temporal (TERM-T020) | Communication (Commitment TERM-M005 deadline), Governance (Obligation TERM-G005 deadline) | P2 |
| TemporalServiceMetric (temporal performance measurement) | Temporal (TERM-T021) | Governance (Obligation TERM-G005 = contractual SLA; metric = clock) | P3 |
| Buffer (deliberate schedule slack) | Temporal (TERM-T022) | — | P4 |
| Cadence (organizational recurring structure) | Temporal (TERM-T023) | Business (sprint/fiscal period boundaries) | P4 |
| SchedulingObjective (optimization goal) | Temporal (TERM-T024) | Compute (solver objective function) | P4 |
| TemporalEnvelope (AI scheduling authority) | Temporal (TERM-T025) | Business (chained from TERM-030), Knowledge (chained from TERM-K022) | P3 |
| SchedulingPolicy (declarative scheduling rule) | Temporal (TERM-T026) | Governance (Norm temporal_constraint_spec consumed as compliance-type policy) | P3 |
| CalendarSystem (date/time interpretation rules) | Temporal (TERM-T027) | — | P4 |
| Capacity (aggregate resource availability) | Temporal (TERM-T028) | Knowledge (demand forecast Propositions) | P1 |
| TransitionTime (inter-activity preparation) | Temporal (TERM-T029) | Physical (equipment changeover), Design (FabricationMethod changeover) | P4 |
| Waitlist (ordered scheduling queue) | Temporal (TERM-T030) | — | P4 |
| CoordinateReferenceSystem (spatial datum/projection) | Spatial (TERM-S001) | — | P4 |
| Location (geographic point) | Spatial (TERM-S002) | Physical (PhysicalAsset position), Business (Organization locations), Temporal (TransitionTime endpoints) | P4 |
| Address (structured location reference) | Spatial (TERM-S003) | Business (customer/vendor addresses) | P4 |
| SpatialGeometry (geographic shape) | Spatial (TERM-S004) | — | P4 |
| SpatialFeature (named entity with extent) | Spatial (TERM-S005) | Knowledge (geographic provenance) | P4 |
| Layer (thematic feature collection) | Spatial (TERM-S006) | — | P4 |
| SpatialDataset (versioned spatial snapshot) | Spatial (TERM-S007) | — | P4 |
| Raster (continuous field grid) | Spatial (TERM-S008) | — | P4 |
| SpatialRelationship (topological/metric relation) | Spatial (TERM-S009) | — | P4 |
| SpatialConstraint (spatial placement rule) | Spatial (TERM-S010) | Governance (zoning norms applied as constraints) | P3 |
| SpatialIndex (hierarchical spatial partitioning) | Spatial (TERM-S011) | — | P4 |
| SpatialNetwork (connected routing graph) | Spatial (TERM-S012) | — | P4 |
| NetworkSegment (traversable edge) | Spatial (TERM-S013) | — | P4 |
| Route (origin-destination path) | Spatial (TERM-S014) | Temporal (TransitionTime travel duration) | P4 |
| ServiceArea (reachability extent) | Spatial (TERM-S015) | Business (delivery eligibility) | P4 |
| Zone (geographic region with rules) | Spatial (TERM-S016) | Governance (Jurisdiction geographic extent TERM-G017) | P3 |
| Territory (assigned geographic scope) | Spatial (TERM-S017) | Business (sales territory management) | P4 |
| Boundary (zone dividing line) | Spatial (TERM-S018) | — | P4 |
| Place (culturally significant named location) | Spatial (TERM-S019) | Temporal (CalendarSystem timezone linkage) | P4 |
| GeocodingResult (address↔coordinate translation) | Spatial (TERM-S020) | — | P4 |
| Trajectory (time-ordered movement path) | Spatial (TERM-S021) | Physical (PhysicalAsset relocation), Temporal (duration computation) | P4 |
| Coverage (resource/service geographic extent) | Spatial (TERM-S022) | — | P4 |
| Density (spatial distribution metric) | Spatial (TERM-S023) | — | P4 |
| ProximityRule (distance-based monitoring trigger) | Spatial (TERM-S024) | — | P4 |
| Floor (vertical spatial layer) | Spatial (TERM-S025) | — | P4 |
| IndoorSpace (navigable room/corridor) | Spatial (TERM-S026) | Temporal (SchedulableResource for room booking) | P4 |
| SpatialEnvelope (AI spatial authority) | Spatial (TERM-S027) | Business (chained from TERM-030), Temporal (chained from TERM-T025) | P3 |
| SpatialPolicy (spatial operation rule) | Spatial (TERM-S028) | Governance (compliance norms as spatial policies) | P3 |
| SpatialAccuracy (positional quality metadata) | Spatial (TERM-S029) | Knowledge (accuracy claims as Proposition TERM-K001) | P1 |
| SpatialChange (spatial disruption event) | Spatial (TERM-S030) | Temporal (Disruption TERM-T013 triggered by spatial change), Business (delivery replanning) | P2 |
| **DISAMBIGUATION** | | | |
| Schedule (time-based trigger) | Business (TERM-017) | Temporal (recurring type delegates to Recurrence TERM-T005) | P4 — Different concepts sharing a name. Business TERM-017 = event trigger ("at T / every P / when C"). Temporal TERM-T010 = constraint-satisfaction result (assignment of Activities to TimeWindows and Resources). |
| Reservation (commercial agreement) vs Booking (temporal allocation) | Business (TERM-023) / Temporal (TERM-T004) | Each references the other | P4 — Booking = temporal slot allocation (availability checking, conflict detection). Reservation = commercial lifecycle (pricing, cancellation, payment). Reservation references Booking for temporal fields; Booking carries commercial_agreement_ref → Reservation. |
| SLA: TemporalServiceMetric (clock) vs Obligation (contract) | Temporal (TERM-T021) / Governance (TERM-G005) | Each references the other | P3 — TemporalServiceMetric measures temporal performance (target duration, percentiles, breach detection). Obligation defines contractual terms (penalties, remediation). Metric emits breach events; Governance processes through Obligation→Violation→Sanction lifecycle. |
| Geometry (artifact shape) vs SpatialGeometry (geographic shape) | Design (TERM-D006) / Spatial (TERM-S004) | Each may co-exist for same real-world entity | P4 — Design Geometry = artifact shape in local coordinate system (cartesian/cylindrical/spherical/fractional_crystal/internal_molecular). Spatial SpatialGeometry = geographic shape in Earth-referenced coordinate system (WGS84/UTM/projected). Coordinate system enums have zero overlap. A building has BOTH a Design Geometry (architectural form) AND a Spatial SpatialGeometry (site position on Earth). For BIM: Design owns the IFC building model geometry; Spatial owns the cadastral map footprint. |
| Zone (operational safety grouping) vs Zone (geographic region) | Physical (TERM-P018) / Spatial (TERM-S016) | Physical Zone may reference Spatial Zone for geographic context | P4 — Physical Zone = operational safety/security grouping within a facility (IEC 62443 zones, hazardous areas per IEC 60079; sensor/actuator scope). Spatial Zone = geographic region with associated policies (administrative boundaries, land-use zones, delivery areas; city-scale and above). Physical Zone operates at facility level with safety semantics; Spatial Zone operates at geographic level with policy semantics. |

---

## 8. Federation Protocol

### 8.0 Scope and Non-Goals

**Federation** is bilateral cross-organization interaction via consent-governed, privacy-preserving data exchange. All nine substrate specifications promise a three-tier architecture (Edge / Organization / Federation) but defer the federation tier to this section.

Federation is **infrastructure, not a substrate.** The 10TH-SUBSTRATE-GAP-ANALYSIS concluded that cross-org interaction decomposes entirely to existing primitives — no new TERM-* identifiers are introduced. Federation concepts are expressed as **composition schemas** that combine existing primitives from GOVERNANCE (consent, norms, permissions), BUSINESS (organizations), COMMUNICATION (protocols, speech acts), and other substrates as needed.

**Non-goals:**
- Sovereign norm conflict resolution. When two organizations' norms conflict at federation boundaries, the result remains `requires_human_determination` (per GOVERNANCE §15).
- Cross-organization ACID consistency. Federation provides advisory coordination, not distributed transactions.
- Replacing internal governance. Federation agreements supplement — never override — each organization's internal envelope chain.

---

### 8.1 Bilateral Trust Establishment

#### 8.1.1 FederationAgreement Schema

A **FederationAgreement** is a composition of existing primitives that formalizes bilateral trust between two organizations.

```
FederationAgreement {
  agreement_id:          UUID,
  status:                "proposed" | "active" | "suspended" | "revoked" | "expired",
  trust_level:           "exploratory" | "operational" | "strategic",
  symmetry:              "symmetric" | "asymmetric",

  // Composed from existing primitives
  organization_a:        Reference<Organization TERM-005>,
  organization_b:        Reference<Organization TERM-005>,
  consent_a:             Reference<ConsentRecord TERM-G027>,    // Org A's informed agreement
  consent_b:             Reference<ConsentRecord TERM-G027>,    // Org B's informed agreement
  bilateral_norm:        Reference<Norm TERM-G001>,             // mutual obligations
  policy_binding:        Reference<PolicyBinding TERM-G004>,    // binds norm to federation scope
  jurisdiction_mappings: Reference<JurisdictionMapping TERM-G019>[],

  // Federation-specific configuration
  exchange_rules:        SubstrateExchangeRule[],               // per §8.2
  event_bridges:         Reference<EventBridgeConfig>[],        // per §8.3
  identity_bridge:       Reference<IdentityBridge>,             // per §8.5
  revocation_protocol:   RevocationProtocol,                    // per §8.1.3

  effective_from:        ISO-8601,
  expires_at:            ISO-8601?,
  review_cadence:        duration                               // periodic ComplianceAssessment interval
}
```

**Status lifecycle:** `proposed → active → suspended → revoked` or `proposed → active → expired`. Suspension is reversible; revocation is terminal.

#### 8.1.2 Lifecycle Protocol

1. **Proposal.** Organization A creates a FederationAgreement with status `proposed` and transmits it via COMMUNICATION Protocol (TERM-M007) negotiation. Emits `substrate.governance.federation.proposed`.
2. **Negotiation.** Counter-proposals are exchanged as Speech Acts (TERM-M002) within a negotiation Discourse (TERM-M001). Each counter-proposal modifies exchange_rules, trust_level, or scope. Terminates with accept or reject.
3. **Activation.** Both organizations create ConsentRecords (TERM-G027), instantiate PolicyBindings (TERM-G004), and configure event bridges (§8.3) and identity bridges (§8.5). Status transitions to `active`. Emits `substrate.governance.federation.activated`.
4. **Steady State.** Data exchange proceeds per SubstrateExchangeRules (§8.2). Periodic ComplianceAssessment (TERM-G009) evaluates bilateral norm adherence at `review_cadence` intervals.

#### 8.1.3 Revocation Protocol

```
RevocationProtocol {
  trigger_types:              ("mutual_agreement" | "unilateral_with_notice" |
                               "breach_immediate" | "regulatory_order")[],
  notice_period:              duration,          // per trigger type
  data_retention_policy:      duration,          // how long received data is kept post-revocation
  in_flight_handling:         "complete" | "drop" | "quarantine",
  post_revocation_obligations: Reference<Norm TERM-G001>[]    // per jurisdiction
}
```

**Rules:**
- Trigger `breach_immediate` requires zero notice_period and emits `substrate.governance.federation.revoked` immediately.
- Trigger `unilateral_with_notice` emits `substrate.governance.federation.suspended` during the notice period, then `substrate.governance.federation.revoked` at expiry.
- Post-revocation: event bridges are torn down (§8.3.4), identity mappings are invalidated (§8.5), ConsentRecords are marked `fully_revoked`.
- Data already received by the target organization is governed by `post_revocation_obligations`, which vary by jurisdiction per JurisdictionMapping (TERM-G019).

---

### 8.2 Per-Substrate Privacy-Granular Exchange Rules

#### 8.2.1 SubstrateExchangeRule Schema

```
SubstrateExchangeRule {
  substrate:            "business" | "knowledge" | "compute" | "communication" |
                        "physical" | "design" | "governance" | "temporal" | "spatial",
  exchange_level:       "none" | "anonymized_metrics" | "filtered_summary" | "consent_gated_detail",
  privacy_filter:       PrivacyFilter,
  consent_record_ref:   Reference<ConsentRecord TERM-G027>,
  data_directions:      ("a_to_b" | "b_to_a" | "bidirectional")[],
  rate_limits: {
    max_events_per_hour: integer?,
    max_payload_bytes_per_day: integer?
  }
}
```

#### 8.2.2 PrivacyFilter Schema

```
PrivacyFilter {
  field_redactions:       string[],            // field paths to remove before transmission
  precision_degradation: {
    spatial_precision:    "city" | "district" | "street" | "building" | "exact"?,
    temporal_precision:   "day" | "hour" | "minute" | "exact"?,
    numeric_rounding:     integer?             // decimal places
  },
  aggregation_rules: {
    min_group_size:       integer?,            // suppress groups smaller than this
    aggregation_period:   duration?            // time window for aggregation
  },
  k_anonymity_k:          integer?,            // minimum anonymity set size
  temporal_delay:         duration?,           // delay before data release
  differential_privacy: {
    epsilon:              float?,              // privacy budget
    delta:                float?               // failure probability
  }
}
```

The PrivacyFilter generalizes the privacy patterns from SPATIAL SpatialPolicy (TERM-S028) to all substrates.

#### 8.2.3 Per-Substrate Exchange Table

| Substrate | `none` | `anonymized_metrics` | `filtered_summary` | `consent_gated_detail` |
|-----------|--------|---------------------|--------------------|-----------------------|
| **BUSINESS** | — | Org name, public endpoint | + jurisdiction, service catalog | + anonymized transaction summaries |
| **KNOWLEDGE** | — | Shared ontology schemas | + proposition summaries (title, domain, confidence range) | + full propositions with provenance chain |
| **COMPUTE** | — | Resource types, capabilities | + capacity ranges, pricing tiers | + federated job submission (TERM-C004) |
| **COMMUNICATION** | — | Protocol compatibility | + shared Discourse creation (TERM-M001) | + full cross-org Discourse participation |
| **PHYSICAL** | **Default** | Anonymized benchmarks (no serial numbers, no locations) | + anonymized maintenance knowledge | **NO actuator Commands (TERM-P005) ever cross federation.** |
| **DESIGN** | — | Published standards, certifications | + shared component libraries (public specs only) | + IP-protected supply chain exchange with bilateral authorization |
| **GOVERNANCE** | — | Jurisdiction declarations, Authority IDs | + anonymized compliance status | + cross-org ComplianceAssessment (TERM-G009) |
| **TEMPORAL** | **Default** | — | busy/free Availability (TERM-T003) per TRUST-T004 | + slots_only or full_detail with ConsentRecord |
| **SPATIAL** | **Default** | — | Precision-degraded features (city-level, k-anonymity) | + building-level precision with bilateral SpatialPolicy (TERM-S028) |

**Rules:**
- **R8.2-1:** Trust level gates exchange level. `exploratory` permits up to `filtered_summary`. `operational` and `strategic` permit `consent_gated_detail`.
- **R8.2-2:** Substrates marked **Default** `none` require explicit opt-in — no data crosses without a SubstrateExchangeRule with `exchange_level` above `none`.
- **R8.2-3:** The exchange table defines maximums. Actual exchange may be more restrictive per PrivacyFilter configuration.
- **R8.2-4:** **PHYSICAL actuator Commands (TERM-P005) NEVER cross the federation boundary.** This is an absolute prohibition, not subject to trust level or consent override. Physical safety is non-negotiable.
- **R8.2-5:** DESIGN proprietary data (trade secrets, unpublished IP) NEVER crosses federation without explicit bilateral authorization in the FederationAgreement.
- **R8.2-6:** PrivacyFilter is evaluated at the **sender** BEFORE data leaves the source organization. The target organization never sees pre-filtered data.
- **R8.2-7:** Asymmetric trust (`symmetry: "asymmetric"` in FederationAgreement) permits different exchange levels per direction. Each `data_directions` entry in SubstrateExchangeRule can specify a different `exchange_level`.

---

### 8.3 Federated Event Bus Bridging

#### 8.3.1 EventBridgeConfig Schema

```
EventBridgeConfig {
  bridge_id:            UUID,
  agreement_ref:        Reference<FederationAgreement>,
  source_org:           Reference<Organization TERM-005>,
  target_org:           Reference<Organization TERM-005>,
  status:               "active" | "draining" | "suspended" | "torn_down",

  topic_allowlist:      string[],              // explicit topic patterns permitted
  topic_denylist:       string[],              // explicit topic patterns denied
  privacy_filter_ref:   Reference<PrivacyFilter>,
  consent_gate:         Reference<ConsentRecord TERM-G027>,
  delivery_mode:        "push_immediate" | "batch_periodic" | "on_demand_pull",
  batch_interval:       duration?,             // only for batch_periodic

  created_at:           ISO-8601,
  last_active_at:       ISO-8601
}
```

#### 8.3.2 Bridge Mechanics

Events crossing federation boundaries are wrapped in a **FederatedEventEnvelope:**

```
FederatedEventEnvelope {
  federation_event_id:  UUID,                  // new ID for the federated event
  agreement_ref:        Reference<FederationAgreement>,
  bridge_ref:           Reference<EventBridgeConfig>,
  source_org_id:        UUID,                  // originating organization
  target_org_id:        UUID,                  // destination organization

  // The original event, post-privacy-filter
  payload:              object,                // original event with PrivacyFilter applied

  // Federation trace context
  trace_id:             string,                // new span linked to source trace
  federation_timestamp: ISO-8601               // when the bridge forwarded the event
}
```

**Rules:**
- **R8.3-1:** The source organization's internal `event_id` is NOT included in the FederatedEventEnvelope. The target organization sees only `federation_event_id`.
- **R8.3-2:** The source organization's internal `caused_by` chain is NOT exposed. Target-side `caused_by` references `federation_event_id` values, not source-side `event_id` values.
- **R8.3-3:** PrivacyFilter is applied BEFORE the event leaves the source organization. The bridge applies the filter referenced by `privacy_filter_ref`.
- **R8.3-4:** ConsentGate is verified BEFORE forwarding. If `consent_gate` references a revoked ConsentRecord, the event is dropped and `substrate.governance.consent.gate_blocked` is emitted.
- **R8.3-5:** A new `trace_id` span is created for the federated event, linked to the source trace. This provides cross-org auditability without exposing internal topology.
- **R8.3-6:** `push_immediate` delivery provides at-most-once guarantee. `batch_periodic` and `on_demand_pull` provide at-least-once guarantee (consumers must be idempotent per §3).
- **R8.3-7:** Each EventBridgeConfig is unidirectional. Bidirectional bridging requires two EventBridgeConfig instances (one per direction).

#### 8.3.3 Topic Routing

The `topic_allowlist` and `topic_denylist` in EventBridgeConfig determine which events cross the bridge.

**Rules:**
- **R8.3-8:** Denylist overrides allowlist. An event matching both a denylist and an allowlist entry is denied.
- **R8.3-9:** Wildcard `substrate.*.*.*` MUST NOT appear in any allowlist. Topic allowlists must be scoped to specific substrates (e.g., `substrate.business.organization.*`).
- **R8.3-10:** Default allowlists per exchange level:
  - `anonymized_metrics`: Only `*.created` and `*.completed` event types.
  - `filtered_summary`: Above plus `*.updated` and `*.status_changed`.
  - `consent_gated_detail`: All event types within the substrate scope, subject to PrivacyFilter.

#### 8.3.4 Consent Revocation Propagation

When a ConsentRecord referenced by an EventBridgeConfig is revoked:

1. Bridge status transitions to `draining`.
2. No new events are accepted for forwarding.
3. In-flight events are handled per `RevocationProtocol.in_flight_handling` (complete, drop, or quarantine).
4. Both organizations are notified via `substrate.governance.federation.bridge_suspended`.
5. Bridge status transitions to `torn_down` after draining completes.

The FederationAgreement's `revocation_protocol` governs the timing and obligations of this process.

---

### 8.4 Cross-Organization Envelope Chaining

#### 8.4.1 The Visiting Agent Problem

When an agent from Organization A operates within Organization B's systems (e.g., submitting a federated compute job, participating in a cross-org discourse), the agent carries authority from its home envelope chain but must also respect the host organization's constraints.

**Fundamental rule:** Effective authority for a visiting agent = intersection(home_envelope_chain, host_guest_permissions, agreement_scope).

#### 8.4.2 FederatedEnvelopeChain Schema

```
EnvelopeChainSummary {
  // Provided by home organization — opaque to host
  home_org:             Reference<Organization TERM-005>,
  substrate_scopes:     string[],              // which substrates the agent has authority in
  max_authority_level:  "read_only" | "propose" | "execute" | "administer",
  constraints_hash:     string,                // cryptographic attestation of home chain
  issued_at:            ISO-8601,
  expires_at:           ISO-8601
}

GuestPermissionSet {
  // Provided by host organization
  host_org:             Reference<Organization TERM-005>,
  agreement_ref:        Reference<FederationAgreement>,
  permissions:          Reference<Permission TERM-G006>[],
  delegations:          Reference<Delegation TERM-G008>[],
  scope_restrictions:   string[],              // further narrowing of host permissions
  valid_from:           ISO-8601,
  valid_until:          ISO-8601               // MUST have expiry — no permanent guest authority
}
```

#### 8.4.3 Authority Computation Rules

**Rules:**
- **R8.4-1:** Effective authority = intersection(home_chain_summary, host_guest_permissions, agreement_exchange_rules). Authority is **triple-bounded** — the most restrictive of the three applies.
- **R8.4-2:** The host NEVER sees the full home envelope chain. The host receives only the EnvelopeChainSummary, which is cryptographically attested but opaque. This preserves internal governance privacy.
- **R8.4-3:** The home organization is responsible for ensuring the EnvelopeChainSummary accurately reflects the agent's actual authority. Misrepresentation is a violation of the bilateral Norm.
- **R8.4-4:** Effective authority computation is performed by the **host** organization. The host intersects the summary with its own GuestPermissionSet and the FederationAgreement scope.
- **R8.4-5:** Deny by default. If no GuestPermissionSet exists for a visiting agent, the agent has **zero authority** in the host organization.
- **R8.4-6:** GuestPermissionSet uses existing Permission (TERM-G006) and Delegation (TERM-G008) primitives. No new permission model is introduced.
- **R8.4-7:** GuestPermissionSets are time-bound (`valid_until` is required). No permanent guest authority is permitted. Maximum duration is governed by the FederationAgreement's trust_level.
- **R8.4-8:** Revocation of the FederationAgreement or either organization's ConsentRecord immediately invalidates all GuestPermissionSets and EnvelopeChainSummaries issued under that agreement.

#### 8.4.4 Regulatory Authority Exception

Regulators are NOT federation peers. They do not use FederationAgreements.

Regulatory access operates via the existing GOVERNANCE integration contract IFC-G009 (Regulatory/Compliance Interface), scoped by Jurisdiction (TERM-G017). A regulator's authority derives from jurisdictional law, not bilateral consent. Therefore:

- **R8.4-9:** Regulatory access does NOT require a FederationAgreement or bilateral ConsentRecords.
- **R8.4-10:** Regulatory scope is bounded by Jurisdiction (TERM-G017), not by SubstrateExchangeRules.
- **R8.4-11:** The federation protocol's PrivacyFilters do NOT apply to regulatory access. Regulators receive data per their jurisdictional authority.
- **R8.4-12:** Clear separation: **federation = peers** (consent-governed, bilateral, symmetric or asymmetric by agreement); **regulation = authority-and-subject** (jurisdiction-governed, unilateral, inherently asymmetric).

---

### 8.5 Federated Identity Bridging

#### 8.5.1 IdentityBridge Schema

```
IdentityBridge {
  bridge_id:              UUID,
  agreement_ref:          Reference<FederationAgreement>,
  home_idp_endpoint:      URI,                 // home organization's Identity Provider
  host_idp_endpoint:      URI,                 // host organization's Identity Provider
  claim_mappings:         ClaimMapping[],       // how home claims translate to host claims
  token_exchange_config:  TokenExchangeConfig,
  audit_trail_ref:        Reference<AuditTrail TERM-G011>,
  status:                 "active" | "suspended" | "invalidated"
}

ClaimMapping {
  home_claim:             string,              // claim name in home IdP
  host_claim:             string,              // equivalent claim in host IdP
  transformation:         "direct" | "mapped" | "suppressed",
  mapping_table:          object?              // for "mapped" transformations
}

TokenExchangeConfig {
  protocol:               "oauth2_token_exchange" | "saml_assertion",
  max_token_lifetime:     duration,            // MUST NOT exceed 1 hour (R8.5-1)
  refresh_permitted:      boolean,
  audience_restriction:   string               // host org's service identifier
}
```

Each organization retains its own Identity Provider. The IdentityBridge creates a mapping between them — it does NOT merge, replicate, or synchronize identity stores.

#### 8.5.2 Token Exchange Protocol

1. **Home authentication.** Agent authenticates with home organization's IdP.
2. **Present to bridge.** Agent presents home token to the IdentityBridge.
3. **Validate.** Bridge validates the home token against `home_idp_endpoint`.
4. **Create federated token.** Bridge creates a federation-scoped token with claims transformed per `claim_mappings` and audience restricted to `audience_restriction`.
5. **Host validates.** Host organization's services validate the federated token against `host_idp_endpoint` with the bridge as a trusted issuer.

**Rules:**
- **R8.5-1:** Maximum federated token lifetime is 1 hour. Tokens must be re-issued for longer operations.
- **R8.5-2:** The host organization NEVER accesses the home IdP directly. All identity exchange flows through the IdentityBridge.
- **R8.5-3:** Token exchange is logged in the AuditTrail (TERM-G011) referenced by the IdentityBridge.
- **R8.5-4:** Suspension of the IdentityBridge immediately invalidates all outstanding federated tokens.

#### 8.5.3 Identity Privacy

**Rules:**
- **R8.5-5:** Default identity is **pseudonymized**. The federated token carries `pseudonym = hash(agent_id + agreement_id)` rather than the actual `agent_id`. This prevents cross-agreement identity correlation.
- **R8.5-6:** De-pseudonymization requires an explicit ConsentRecord (TERM-G027) with `purpose: "identity_disclosure"` AND audit logging of every de-pseudonymization event.
- **R8.5-7:** Even with de-pseudonymization, the host organization receives only the claims permitted by `claim_mappings`. Suppressed claims are never transmitted.

#### 8.5.4 Multi-Party Federation

**Rules:**
- **R8.5-8:** Multi-party federation is modeled as bilateral pairs. Three organizations (A, B, C) require three FederationAgreements: A↔B, A↔C, B↔C. There is no "consortium agreement" primitive.
- **R8.5-9:** NO transitive trust. A FederationAgreement between A↔B and B↔C does NOT create any trust relationship between A and C. Each pair must establish its own agreement.
- **R8.5-10:** Each bilateral pair has its own EventBridgeConfigs, IdentityBridges, and SubstrateExchangeRules. No sharing of federation infrastructure between pairs.
- **R8.5-11:** Identity is pairwise. Agent pseudonyms are agreement-scoped (`hash(agent_id + agreement_id)`), so the same agent has different pseudonyms in different federation relationships. No transitive identity assertion.
- **R8.5-12:** The O(n²) cost of bilateral federation is acknowledged. For n organizations, n(n-1)/2 agreements are required. Federated trust registries that reduce this cost are deferred to v2.1.

---

### 8.6 Open Question Resolution

This section resolves four open questions from the substrate specifications that were explicitly deferred to federation infrastructure.

**OQ-G008 (GOVERNANCE): "How do GOVERNANCE norms interact across organizational boundaries in federated deployments?"**
→ Resolved by §8.1 (FederationAgreement with bilateral Norm), §8.2 (per-substrate SubstrateExchangeRules with GOVERNANCE exchange levels), and §8.3 (EventBridgeConfig for cross-org governance events). Each organization retains sovereign norm authority; federation creates a bilateral overlay via consent-governed exchange rules, not norm unification.

**OQ-T003 (TEMPORAL): "How does cross-organization scheduling handle privacy constraints when sharing availability across federated deployments?"**
→ Resolved by §8.2.3 (TEMPORAL exchange table: `filtered_summary` provides busy/free Availability per TRUST-T004; `consent_gated_detail` provides slots_only or full_detail with ConsentRecord gating) and §8.2.2 (PrivacyFilter with temporal_precision degradation). Organizations never share raw schedule data at federation boundaries without explicit consent and privacy filtering.

**OQ-S003 (SPATIAL): "How does cross-organization spatial data exchange handle privacy constraints when sharing location data across federated deployments?"**
→ Resolved by §8.2.3 (SPATIAL exchange table: `filtered_summary` provides precision-degraded features at city level with k-anonymity; `consent_gated_detail` provides building-level precision with bilateral SpatialPolicy) and §8.2.2 (PrivacyFilter with spatial_precision degradation and k_anonymity_k). The PrivacyFilter generalizes SPATIAL's existing SpatialPolicy (TERM-S028) privacy types to all substrates.

**OQ-C001 (COMPUTE): "How do federated compute pools manage cross-organization resource sharing while respecting sovereignty?"**
→ Resolved by §8.2.3 (COMPUTE exchange table: `filtered_summary` provides capacity ranges and pricing tiers; `consent_gated_detail` enables federated job submission via Execution TERM-C004). Organizations publish available capacity (not private utilization) and accept federated jobs subject to PrivacyFilter on inputs/outputs and GuestPermissionSet authority bounds. Multi-party computation (MPC) for privacy-preserving joint computation remains a research item beyond this specification.

---

### 8.7 Limitations

**LIM-F001: Sovereign norm conflicts.** When two organizations' norms conflict at federation boundaries (e.g., conflicting data retention requirements, incompatible compliance standards), the result is `requires_human_determination` per GOVERNANCE §15. This specification provides the infrastructure to detect such conflicts (via cross-org ComplianceAssessment) but does not provide automated resolution. Norm sovereignty is a non-negotiable design principle.

**LIM-F002: Cross-organization consistency.** Federation provides advisory coordination, not distributed ACID consistency. When a cross-org workflow involves state changes in both organizations, each organization's changes are locally consistent. Cross-org consistency is eventual and advisory — if a rollback is needed, the federation event bus communicates the rollback, but each organization handles its own state recovery independently.

**LIM-F003: Physical control prohibition.** Actuator Commands (TERM-P005) NEVER cross the federation boundary. This is absolute: no trust level, no consent override, no regulatory exception permits remote physical actuation across organizational boundaries. Physical safety requires local authority with local accountability.

**LIM-F004: Bilateral model scalability.** The O(n²) cost of pairwise federation agreements limits practical federation to moderate numbers of organizations. For n=10, 45 agreements are required; for n=50, 1,225. Federated trust registries, consortium governance patterns, and hierarchical federation models that reduce this cost are deferred to v2.1.

**LIM-F005: Cascading revocation.** In multi-party federation (§8.5.4), revoking one bilateral agreement may cascade — if Organization B's service depends on data from both A and C, revoking A↔B may degrade B's ability to fulfill its agreement with C. Cascading impact analysis and mitigation is the responsibility of each organization's internal governance, not the federation protocol.

---

## Changelog

| Date | Version | Change |
|------|---------|--------|
| 2029-06-15 | 1.0 | Initial conventions document. Established shared identity, organization, event bus, tracing, reference format, boundary principles, and ownership table. |
| 2029-08-01 | 1.1 | Added SUBSTRATE-PHYSICAL v1.0. Updated §1 with PhysicalEnvelope in envelope chain (most restrictive). Added "physical" to §3 substrate enum and §5 reference format. Added physical event topic examples. Added 15 PHYSICAL primitives to §7 ownership table. Updated §3 retention note for PHYSICAL (7-year minimum). |
| 2029-12-15 | 1.2 | Added SUBSTRATE-DESIGN v1.0. Updated §1 with DesignEnvelope in envelope chain (between Epistemic and Compute). Added "design" to §3 substrate enum and §5 reference format. Added 6 design event topic examples. Added 27 DESIGN primitives to §7 ownership table. Updated §3 retention note for DESIGN (100-year minimum). Updated §6 P3 with DESIGN enforcement note. |
| 2030-03-01 | 1.3 | Added SUBSTRATE-GOVERNANCE v1.0. Updated §1 with GovernanceEnvelope in envelope chain (between Business and Epistemic). Added "governance" to §3 substrate enum and §5 reference format. Added 7 governance event topic examples. Added 27 GOVERNANCE primitives to §7 ownership table. Updated §3 retention note for GOVERNANCE (7-year financial, 30-year safety, indefinite some jurisdictions). Updated §6 P3 with GOVERNANCE enforcement note (adjudication/sanctioning/attestation non-delegable to AI). |
| 2030-06-15 | 1.4 | Added SUBSTRATE-TEMPORAL v1.0. Updated §1 with TemporalEnvelope in envelope chain (between Epistemic and Design). Added "temporal" to §3 substrate enum and §5 reference format. Added 11 temporal event topic examples. Added 30 TEMPORAL primitives to §7 ownership table. Added 3 disambiguation rows to §7 (Schedule name collision, Reservation/Booking split, SLA/TemporalServiceMetric split). Updated §3 retention note for TEMPORAL (7-year minimum for compliance-relevant schedules). Updated §6 P3 with TEMPORAL enforcement note (TemporalEnvelope bounds, proactive labor norm enforcement during schedule creation). |
| 2030-09-15 | 1.5 | Added SUBSTRATE-SPATIAL v1.0. Updated §1 with SpatialEnvelope in envelope chain (between Temporal and Design). Added "spatial" to §3 substrate enum and §5 reference format. Added 17 spatial event topic examples. Added 30 SPATIAL primitives to §7 ownership table. Added 2 disambiguation rows to §7 (Geometry/SpatialGeometry split — Design artifact shape vs Spatial geographic shape with zero coordinate system overlap; Zone/Zone split — Physical operational safety grouping vs Spatial geographic region with policies). Updated §3 retention note for SPATIAL (cadastral 100+ years, fleet positions 90 days). Updated §6 P3 with SPATIAL enforcement note (SpatialEnvelope bounds, GOVERNANCE zoning norms applied as SpatialConstraints). |
| 2031-02-10 | 2.0 | Added §8 Federation Protocol. Defines bilateral trust establishment (FederationAgreement), per-substrate privacy-granular exchange rules (SubstrateExchangeRule, PrivacyFilter), federated event bus bridging (EventBridgeConfig, FederatedEventEnvelope), cross-organization envelope chaining (EnvelopeChainSummary, GuestPermissionSet), and federated identity bridging (IdentityBridge). 8 composition schemas — all decompose to existing TERM-* primitives (252 primitive count unchanged). Added 6 federation event topics to §3. Resolves OQ-G008, OQ-T003, OQ-S003, OQ-C001. Establishes 5 limitations (LIM-F001–F005). Updated version header and Applies to line for v2.1/v1.1 spec parity. |
