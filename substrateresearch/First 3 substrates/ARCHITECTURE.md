# SUBSTRATE Architecture Guide

## For Coding Agents and Human Contributors

**Last updated:** 2026-02-09
**Status:** Living document. Amend, do not rewrite.

---

## System Purpose

SUBSTRATE is a universal engine for business software. It provides 31 primitives (entities, transactions, workflows, reservations, rules, etc.) that compose into any business application through configuration rather than code.

SUBSTRATE is a **runtime**, not an application. Think of it like a database or a web server — you don't modify it to build a specific product. You build products **on top of it** by producing configurations and UIs that talk to its API.

---

## The Three-Layer Architecture

```
┌─────────────────────────────────────────────────────┐
│  ARTIFACT LAYER (what agents produce)                │
│  Coding agents work HERE.                            │
│                                                      │
│  ┌──────────────┐  ┌───────────┐  ┌──────────────┐  │
│  │ Configuration │  │ UI App    │  │ Integrations │  │
│  │ (YAML file)   │  │ (React /  │  │ (small       │  │
│  │               │  │  mobile)  │  │  scripts)    │  │
│  └──────┬───────┘  └─────┬─────┘  └──────┬───────┘  │
│         │                │               │           │
├─────────┼────────────────┼───────────────┼───────────┤
│  API SURFACE (IFC-001 through IFC-011)               │
│  ── the ONLY contact point ──                        │
│  See: OpenAPI spec at /openapi.json                  │
│  See: substrate-spec.md Section 6 for contracts      │
├──────────────────────────────────────────────────────┤
│  SUBSTRATE ENGINE (agents NEVER touch this)           │
│                                                      │
│  ┌──────────┐ ┌────────────┐ ┌────────────────────┐ │
│  │ Entity   │ │ Transaction│ │ Workflow Engine     │ │
│  │ Engine   │ │ Engine     │ │                     │ │
│  ├──────────┤ ├────────────┤ ├────────────────────┤ │
│  │ Event    │ │ Rule       │ │ Permission Engine  │ │
│  │ Store    │ │ Engine     │ │                     │ │
│  ├──────────┤ ├────────────┤ ├────────────────────┤ │
│  │ Query    │ │ Schedule   │ │ Agent Envelope     │ │
│  │ Engine   │ │ Engine     │ │ Enforcement        │ │
│  └──────────┘ └────────────┘ └────────────────────┘ │
│                                                      │
│  Tests: 490 | Language: Rust | DB: SQLite            │
│  DO NOT MODIFY without explicit instruction.         │
└──────────────────────────────────────────────────────┘
```

### Layer 1: SUBSTRATE Engine (off limits to agents)

The Rust codebase. Contains: entity engine, transaction/ledger engine, workflow engine, rule/expression engine, event store (BLAKE3 hash-chained), permission engine, agent envelope enforcement, and the Axum HTTP API server.

**Agents MUST NOT modify engine code** unless explicitly instructed to work on a specific engine component. The engine is the foundation — it's tested, stable, and correct.

Current engine status:
- Entity Engine: complete (32 tests)
- Transaction Engine: complete (46 tests)
- Rule Engine: complete (112 tests)
- Workflow Engine: complete (29 tests)
- Event Store: complete (20 tests)
- Types: complete (89 tests)
- API Layer: complete (147 tests)
- Server: complete (15 tests)
- **Not yet built:** Reservation Engine, Approval Routing (DEC-004), External System integration endpoints (ACT-005), field-level encryption

### Layer 2: API Surface (the boundary)

~40 REST endpoints on the Axum server. This is the ONLY way to interact with the engine. Features:
- Bearer token authentication with 6 actor types
- Permission enforcement (resource-type gate + per-instance scope)
- Agent Envelopes for AI actor bounded authority
- Rate limiting (org-level + per-agent-envelope)
- Idempotency via `Idempotency-Key` header
- Optimistic locking via `If-Match` header
- RFC 7807 structured errors (`urn:substrate:error:ERR-XXX`)

**All application code — whether written by humans or agents — talks to these endpoints. Nothing reaches below this layer.**

### Layer 3: Artifact Layer (where agents work)

Three types of artifacts that agents produce:

**a) Configuration files** — Declarative YAML describing an entire business setup: entity definitions, workflows, rules, ledgers, views, agent envelopes. The Configuration compiler (`substrate-config`) reads these and emits API calls. Agents produce Configurations; they never write engine code.

**b) UI applications** — Frontend code (React, mobile, etc.) that calls the API and renders responses. Agents build UIs by reading the OpenAPI spec and the Configuration (which tells them the data schema). They never import engine code.

**c) Integration scripts** — Small programs that bridge SUBSTRATE with external systems (Google Calendar, payment terminals, CSV imports). They use the API's integration endpoints.

---

## Rules for Agents Working on This Codebase

### DO:
- Read the OpenAPI spec before making any API calls
- Read the Configuration schema before producing Configurations
- Look at existing Configuration examples (in `/configs/templates/`) before writing new ones
- Validate Configurations using `substrate-config validate` before applying
- Run simulation tests using `substrate-config simulate` after applying
- Write UI code that talks exclusively to API endpoints
- Report gaps in the Configuration language or API as amendment proposals

### DO NOT:
- Modify any file in `substrate-core/`, `substrate-engine/`, `substrate-api/`, or `substrate-server/` unless explicitly told to
- Import engine types directly into application code
- Bypass the API to access the database directly
- Invent new primitive types not in the glossary (see substrate-spec.md Section 3)
- Write Turing-complete logic in Configuration files (the expression language is deliberately limited)
- Store secrets, API keys, or PII in Configuration files

### When you find a gap:
If you need to express something the Configuration language can't handle, do NOT work around it by writing engine code. Instead:
1. Document the gap as an amendment proposal in `docs/amendments/`
2. Describe: what you need, why the current language can't express it, and a suggested addition
3. Continue with a simplified version or flag it for human review

---

## Key Files and Directories

```
substrate/
├── substrate-core/       # Domain types, identifiers, money — DO NOT MODIFY
├── substrate-engine/     # All engines (entity, transaction, workflow, rule, event) — DO NOT MODIFY
├── substrate-api/        # Axum HTTP layer, auth, DTOs — DO NOT MODIFY
├── substrate-server/     # Binary, CLI args, wiring — DO NOT MODIFY
├── substrate-config/     # Configuration compiler (TO BE BUILT)
│   ├── schema/           # JSON Schema for Configuration language
│   ├── src/              # Compiler: validate, apply, diff, export, simulate
│   └── examples/         # Example Configurations
├── configs/
│   ├── templates/        # Reusable industry templates (salon, restaurant, etc.)
│   └── simulations/      # Test scenarios for Configurations
├── apps/                 # Vertical applications (UIs) built on SUBSTRATE
│   └── salon/            # First vertical — nail salon
├── integrations/         # External system integration scripts
├── docs/
│   ├── substrate-spec.md # The canonical system specification (v2)
│   ├── ARCHITECTURE.md   # This file
│   ├── ROADMAP.md        # What to build and in what order
│   └── amendments/       # Spec amendments discovered during implementation
│       └── AMENDMENT-NNN.md
└── openapi.json          # Generated OpenAPI spec (TODO)
```

---

## How Configurations Become Running Software

```
1. Agent (or human) writes salon.yaml         ← Configuration file
2. substrate-config validate salon.yaml        ← Check against JSON Schema
3. substrate-config simulate --config salon.yaml --test salon-tests.yaml  ← Run scenarios
4. substrate-config apply --file salon.yaml --server http://localhost:3000 --api-key xxx
   ↓
   Compiler emits ordered API calls:
     POST /orgs → create organization
     POST /orgs/{id}/definitions → create Client entity
     POST /orgs/{id}/definitions → create Appointment entity
     POST /orgs/{id}/workflows → create appointment_flow
     POST /orgs/{id}/rules → create validation rules
     POST /orgs/{id}/ledgers → create revenue ledger
     ...
   ↓
5. Engine processes API calls normally (same as manual calls)
6. Organization is now operational
7. UI app connects to API, reads entity schemas, renders screens
```

---

## The Spec as Source of Truth

The canonical system specification lives at `docs/substrate-spec.md`. It defines:
- 31 primitives (glossary)
- 26 capabilities (what the system can do)
- 10 invariants (what must always be true)
- 10 forbidden states (what must never happen)
- 6 failure guarantees (what happens when things go wrong)
- 33 test scenarios (how to verify correctness)

**The spec does not change often.** When it does, changes are recorded as amendments in `docs/amendments/` with context and rationale. Amendments are numbered sequentially and appended — the original spec is never rewritten.

The spec evolves when:
- Implementation reveals a gap in the domain model (new primitive or missing rule)
- Reality proves a spec decision wrong (performance, usability, or correctness issue)
- A new vertical reveals a pattern that appears across 3+ industries

The spec does NOT evolve for:
- Implementation convenience (the code adapts to the spec, not vice versa)
- Technology choices (those are in the code, not the spec)
- UI decisions (the spec is silent on UI by design)
