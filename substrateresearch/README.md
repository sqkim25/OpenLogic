# Substrate Research

A formal specification system for ASI-1: nine substrate specifications that decompose organized activity into fundamental dimensions, each answering one irreducible question.

## The Nine Substrates (252 Primitives)

| Substrate | Question | Primitives |
|-----------|----------|------------|
| **BUSINESS** (v2.1) | What does the organization do? | Organizations, Entities, Transactions, Workflows |
| **KNOWLEDGE** (v1.1) | What is true? | Propositions, Evidence, Confidence, Ontologies |
| **COMPUTE** (v1.1) | How to compute? | Computations, Pipelines, Resources, Executions |
| **COMMUNICATION** (v1.1) | How to coordinate discourse? | Discourse, Speech Acts, Commitments, Consensus |
| **PHYSICAL** (v1.1) | How to sense and actuate the world? | Sensors, Actuators, Control Loops, Digital Twins |
| **DESIGN** (v1.1) | What to build? | Components, Specifications, BOMs, Analysis |
| **GOVERNANCE** (v1.1) | What is permitted and required? | Norms, Policies, Compliance, Jurisdiction |
| **TEMPORAL** (v1.1) | When do things happen? | Schedules, Activities, Bookings, Deadlines |
| **SPATIAL** (v1.0) | Where are things? | Locations, Routes, Zones, Service Areas |

## Companion Documents

| Document | Purpose |
|----------|---------|
| **CROSS-SUBSTRATE-CONVENTIONS** (v2.0) | How substrates interoperate (event bus, envelope chain, boundary principles, federation protocol) |
| **10TH-SUBSTRATE-GAP-ANALYSIS** (v1.0) | Structural completeness argument — why 9 substrates is sufficient |
| **SUBSTRATE-COMPOSITION-PATTERNS** (v1.0) | 14 application-level workflows showing how primitives combine to solve real-world problems |

## Key Architecture

- **Envelope chain** (least → most restrictive): Business → Governance → Epistemic → Temporal → Spatial → Design → Compute → Communicative → Physical
- **Event bus**: Cross-substrate communication via `substrate.{name}.{entity_type}.{event_type}` topics
- **Four Master Boundary Principles**: Content/Process, Trigger/Deliver, Define/Enforce, One Owner Many References
- **Substrate catalog is closed** (9 substrates). **Pattern catalog is open** (new compositions can emerge from the same 252 primitives).
